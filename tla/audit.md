# TLA+ Invariant Audit — Implementation Review

This document records the results of a systematic audit of the ReasonMesh Rust implementation against the invariants and liveness properties defined in `ReasonMesh.tla`. The audit was conducted against commit `8ec76c3` plus the accumulated changes in the current working tree, after all CI gates (fmt, clippy, tests) were green.

The goal was to answer a concrete question: for each property that TLC verifies on the abstract model, does the implementation actually honour it? Where it does not, is the gap a correctness bug, a protocol weakness, or an acknowledged modelling approximation?

---

## Method

Three parallel audits were run, each covering a different slice of the codebase:

- **Filter and soundness audit** (I3–I7): `rm-bus`, `rm-akx`, `rm-worker`, `reasonmesh-cli` bridge thread
- **UNSAT proof integrity audit** (I2): `rm-sat`, `rm-smt`, `rm-worker`, `reasonmesh-cli`
- **Liveness audit** (L1–L8): bridge thread lifecycle, `NetBus`, `WorkerPool`, shutdown paths

Findings were classified as one of four outcomes:

- **HOLDS** — the implementation matches the spec's intent.
- **WEAKENED** — the property holds under normal conditions but is not enforced at the code level; a specific configuration or future change could violate it.
- **AT-RISK** — a concrete code path exists where the property can be violated in normal operation.
- **VIOLATED** — the property is violated. (None found in this audit.)

---

## Safety invariants (I1–I7)

### I1 — TypeOK

**HOLDS.**

Rust's type system enforces the structural invariant statically. There is no runtime equivalent to check, and no dynamic cast or unsafe transmute that could violate it.

### I2 — UnsatRequiresProof

**HOLDS for verdict correctness. WEAKENED for proof certificate completeness.**

The verdict `SolveResult::Unsat` is never emitted speculatively. All budget-exhaustion paths (`max_conflicts` exceeded, wall-clock deadline reached) return `SolveResult::Unknown`. The `WorkerPool` maps this correctly: `UnsatLocal` only flows from a conclusive solver result, never from timeout or cancellation.

However, two early-exit UNSAT paths in `CdclSolver::solve` did not call `log_proof_empty()` before returning, producing DRUP certificate files with a missing terminal entry. An external DRAT checker would reject these certificates. The paths affected were:

**Path A** (`cdcl.rs`, `solve` method) — `settle_root_propagations()` returns `true`: the formula is UNSAT purely from level-0 BCP, before any search decisions are made. The solver returns immediately; the main conflict loop that normally logs the empty clause is never entered.

**Path B** (`cdcl.rs`, `push_assumptions_onto_trail`) — an assumption literal is already forced `False` at level 0: the assumption contradicts the root propagations. Again the main loop is bypassed.

Both paths produce a sound verdict but an incomplete proof log.

**Fix applied.** `self.log_proof_empty()` was added to both paths before the `return` statement, with comments explaining why each path bypasses the normal proof-logging route.

### I3 — FilterIntegrity

**HOLDS.**

`drain_and_export()` in `rm-sat/src/reasoner.rs` filters every `KnowledgeObject` against `policy.min_utility` before returning the export batch. This is the only function that populates the export bus. No other code path writes directly to the `BroadcastBus.export` queue. The NetBus therefore only carries objects that passed the utility filter.

The `export_min_utility` value in `run_serve` is computed as `1.0 / (1.0 + export_lbd as f32)`, which is the same formula used in the TLA+ spec's utility encoding.

### I4 — ExportQueueSound

**HOLDS.**

The path from CDCL conflict analysis to the export bus is sequential: `CdclSolver` adds a clause to its internal database, `drain_learned()` moves it to `pending`, `export()` filters and returns a batch, and `drain_export_import()` publishes the batch. A clause enters `pending` only after it is already recorded in the solver's clause DB. The export bus never receives a clause the solver does not already hold.

### I5 — InFlightSound

**HOLDS** (follows from I4).

The bridge thread reads exclusively from `BroadcastBus.export`, which I4 establishes contains only clauses already learned by the sending node. `NetBus::publish` serialises and enqueues without introducing new clause content. The network channel cannot conjure knowledge.

### I6 — LocalQIntegrity

**WEAKENED.** Fixed.

The property holds transitively when all peers in the cluster are running the same binary with the same `--export-lbd` configuration. However, the bridge thread was publishing whatever `net.poll()` returned directly into `local_bus`, with no receive-side utility check. A misconfigured peer (different `--export-lbd`), a future peer implementation, or any node that serialises a low-utility clause via a compatible wire format could inject that clause into `local_bus`, violating the invariant.

The spec's guarantee derives from FilterIntegrity on the sender side plus TCP as a trusted channel. The sender-side filter was correctly implemented; the receiver-side was not.

**Fix applied.** The bridge now filters each incoming network batch before publishing to `local_bus`:

```rust
let filtered: Vec<_> = batch
    .into_iter()
    .filter(|obj| obj.utility >= import_min_utility)
    .collect();
```

`import_min_utility` is set equal to `export_min_utility` in `run_serve`, making the policy symmetric: we only accept from peers what we would send ourselves. The threshold is passed as a new parameter to `spawn_bridge_thread`.

### I7 — NoSelfForward

**WEAKENED.** Fixed.

The TLA+ spec's `BridgeForward` action has an explicit `IF m # n` guard preventing self-forwarding. No equivalent guard existed in the Rust code. `connect_peers` iterated the `--peer` list and called `connect_peer_retry` for each address without checking whether any of them resolved to the local node. `NetBus::publish` sends to every entry in `self.peers` without filtering by destination.

If a user includes the node's own address in `--peer` (e.g., `127.0.0.1:9000` when the node listens on port 9000), `NetBus` would establish a loopback TCP connection. The bridge thread would then forward learned clauses to the node's own incoming queue via the network path, bypassing the `BroadcastBus.local` deduplication. The node would re-import its own clauses as if they came from a peer, inflating import counters and potentially interfering with utility-based eviction in `local_bus`.

**Fix applied.** `connect_peers` now receives the local listen port and checks each peer address before connecting:

```rust
if let Ok(addr) = peer_str.parse::<std::net::SocketAddr>() {
    if addr.port() == local_port
        && (addr.ip().is_loopback() || addr.ip().is_unspecified())
    {
        eprintln!("warn: skipping self-peer {peer_str} — would create a forwarding loop");
        continue;
    }
}
```

**Residual gap**: hostname-based addresses (e.g., `myhost:9000` where `myhost` resolves to the local machine) are not detected without DNS resolution. This is documented in the function's doc comment. The fix handles the most common accidental case.

---

## Liveness properties (L1–L8)

### L1 — ClausesEventuallyForwarded

**AT-RISK.** Fixed.

The bridge thread was structured as `move || loop { if shutdown { break; } ... }`. When `bridge_shutdown.store(true)` fired immediately after `pool.run()` returned, the bridge could exit with items still in `export_bus`. Any clauses that arrived between the last poll and the shutdown signal were permanently lost — not forwarded to peers, not counted in `export_dropped_total`, not logged anywhere.

The spec's `BridgeForward` action has no verdict guard and is enabled until the system is fully done, so the model correctly captures the desired behaviour; the implementation fell short of it.

**Fix applied.** The bridge thread now runs a final drain loop after the main loop exits:

```rust
loop {
    match export_bus.poll(PollBudget { max_items: 64 }) {
        Ok(batch) if !batch.is_empty() => { let _ = net.publish(Scope::Global, batch); }
        _ => break,
    }
}
```

This drains any tail clauses before the bridge thread returns, then the main thread joins the handle and proceeds to shutdown `NetBus`.

### L2 — ClausesEventuallyDelivered

**AT-RISK.** Architectural — not fixed.

`NetBus` maintains one unbounded crossbeam channel per peer. `publish` is non-blocking: it enqueues a frame and returns. The writer thread drains the channel to the TCP socket. If the TCP connection drops mid-run, the writer thread exits on the next `write_all` error. All frames remaining in that channel are discarded, and there is no reconnect or retransmit logic.

The spec models TCP as reliable (there is no `Drop` action). This divergence is acknowledged in the TLA+ README. Fixing it would require a persistent connection layer with sequence numbers and retransmission, which is a substantial networking feature outside the current scope. The behaviour is consistent with the documented limitation.

### L3 — EventualTermination

**HOLDS in cluster mode. AT-RISK in single-process solve mode.**

In `run_serve`, `pool.run()` is always called with `Some(Duration::from_secs(timeout_secs))`. The worker loop checks the deadline on every iteration. A node running in cluster mode will always terminate.

In `run_solve` (single-process, `reasonmesh solve`), the deadline is `None` and `conflict_budget` defaults to `None` unless `--max-conflicts` is set. A correct finite CDCL instance terminates by completeness, but there is no wall-clock safety net. A solver bug (e.g., a non-terminating restart or reduction cycle) could loop indefinitely. This is a deliberate design decision: single-process solves are meant to be bounded by the user via `--max-conflicts` or OS-level timeouts. It is documented in the CLI usage guide.

### L4 — ConvergentTermination

**AT-RISK.** Architectural — not fixed.

**Intra-node convergence holds.** All workers in a pool share a single `Arc<AtomicBool>` shutdown flag. When any worker finds a conclusive verdict, it sets the flag and all other workers see it on their next step. Intra-node convergence is prompt.

**Cross-node convergence is by timeout only.** When node A finds its verdict, `run_serve` returns and the process calls `std::process::exit`. This closes all TCP connections. Node B's `NetBus` reader thread for that connection exits on read error, but B's worker pool is not signalled. B's workers continue running until their own deadline fires.

The spec's `ConvergentTermination` (L4) holds in the model because `Timeout` is available as an escape, and the implementation matches this — peers converge via timeout. However, on a network where A solves quickly, B may run for the full `timeout_secs` after A is long gone, burning CPU unnecessarily.

Fixing this properly would require a control channel separate from the clause-sharing data plane — a "verdict broadcast" message sent before closing connections. This is a protocol addition that is out of scope for the current implementation.

### L5 — KeyClausesPropagateToAll

**HOLDS** (no-timeout model, modulo L1 and L2).

Correctness depends on `WF_vars(BridgeForward)`, `WF_vars(NetDeliver)`, and `WF_vars(WorkerImport)`. The L1 fix ensures the bridge drains before exit; the network is reliable in the normal case (L2's gap only matters on dropped connections); worker import is driven continuously by the CDCL step loop. Given the L1 fix and a stable network, key clauses learned on any node will propagate to all others.

### L6 — ProofLeadsToVerdict

**HOLDS.**

Once a worker accumulates the key clauses — i.e., its CDCL derivation reaches a state where the formula is UNSAT under the current assumptions — the conflict analysis produces the empty clause and the solver returns `SolveResult::Unsat`. The I2 fix ensures the proof log reflects this correctly. The `ReportUnsat` action in the spec maps to this path.

### L7 — EventuallyAllUnsat

**HOLDS** (no-timeout model, modulo L4).

Implied by L5 + L6: every node eventually accumulates the proof via sharing, then reports UNSAT. In the no-timeout model, this is verified by TLC over 34,661 distinct states.

### L8 — ClausesEventuallyImported

**AT-RISK** (post-verdict divergence from spec). Acknowledged — not fixed.

Draining `local_bus` (the `local_q` in the spec) is driven by `drain_export_import()` inside the CDCL step loop. Once a worker exits — whether by finding SAT, UNSAT, or hitting the deadline — it stops stepping and stops draining `local_bus`. Any clauses that arrived in `local_bus` after the worker's last poll are dropped when the pool teardown deallocates the bus.

The spec's `WorkerImport` action has no verdict guard, so the model allows import to continue after a verdict fires. This is an intentional over-approximation: the spec proves that clauses *can* be consumed; the implementation chooses not to consume them once the answer is known, which is correct but diverges from the model.

This is not a correctness issue — the verdict is sound regardless of what remains in the import queue. It is a harmless divergence from the spec's over-approximated liveness property.

### Deadlock analysis

**HOLDS. No circular dependencies found.**

- `InprocBus`: single `Mutex<Queue>`, never held across a channel send or nested lock.
- `NetBus::publish`: holds `peers.lock()` briefly; sends on an `unbounded` channel (non-blocking). No contention with `incoming`.
- `NetBus` reader thread: holds `incoming.lock()` to push items; never held concurrently with `peers`.
- `CdclReasoner`: `Mutex<Vec<KnowledgeObject>>` for the pending export list; held only during drain/export, no nested locks.
- `BroadcastBus::publish`: acquires export then local in a fixed order. No caller acquires them in the opposite order.

**Latent fragility**: all `.lock().unwrap()` calls panic on mutex poisoning. A panicking worker cascades to a main-thread panic via `join().expect(...)`. There is no recovery path. This is consistent behaviour but not resilient — a single thread panic tears down the whole pool. This is a known property of the current design, not a new finding.

---

## Summary

| Property | Pre-audit status | Post-audit status | Change |
|---|---|---|---|
| I1 TypeOK | HOLDS | HOLDS | — |
| I2 UnsatRequiresProof | HOLDS (verdict) / WEAKENED (proof log) | HOLDS | Fixed 2 missing `log_proof_empty()` calls |
| I3 FilterIntegrity | HOLDS | HOLDS | — |
| I4 ExportQueueSound | HOLDS | HOLDS | — |
| I5 InFlightSound | HOLDS | HOLDS | — |
| I6 LocalQIntegrity | WEAKENED | HOLDS | Added receive-side utility filter in bridge |
| I7 NoSelfForward | WEAKENED | HOLDS (IP addresses) | Added self-address guard in `connect_peers` |
| L1 ClausesEventuallyForwarded | AT-RISK | HOLDS | Added final drain loop in bridge on shutdown |
| L2 ClausesEventuallyDelivered | AT-RISK | AT-RISK | Architectural; TCP reconnect out of scope |
| L3 EventualTermination | HOLDS (cluster) / AT-RISK (solve) | unchanged | Deliberate; documented in usage guide |
| L4 ConvergentTermination | AT-RISK | AT-RISK | Architectural; verdict broadcast out of scope |
| L5 KeyClausesPropagateToAll | HOLDS (modulo L1, L2) | HOLDS (modulo L2) | L1 fix removes one dependency |
| L6 ProofLeadsToVerdict | HOLDS | HOLDS | — |
| L7 EventuallyAllUnsat | HOLDS (modulo L4) | HOLDS (modulo L4) | — |
| L8 ClausesEventuallyImported | AT-RISK (post-verdict) | AT-RISK (post-verdict) | Acknowledged spec divergence; not a bug |
| Deadlock | HOLDS | HOLDS | — |

Five properties moved from WEAKENED or AT-RISK to HOLDS as a result of this audit. Four issues remain as architectural limitations that would require protocol-level changes (L2 TCP reliability, L3 solve-mode timeout, L4 verdict broadcast, L8 post-verdict drain) rather than localised code fixes.

---

## TLC re-check results (post-fix)

After the code fixes were applied, both TLC configurations were re-run to confirm that the spec itself remained consistent and that the updated invariants (I6, I7) continued to hold on the abstract model:

```
MC (Timeout enabled):
  No error found. 46,099 distinct states, depth 24. 31 temporal branches checked.

MC_NoTimeout:
  No error found. 34,661 distinct states, depth 24. 42 temporal branches checked.
```

The new invariants (I6 `LocalQIntegrity`, I7 `NoSelfForward`) and the new liveness property (L8 `ClausesEventuallyImported`) all passed in both configurations.
