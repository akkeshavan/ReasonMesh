# Cube-and-Conquer Implementation Plan

## Motivation

Portfolio parallelism does not help UNSAT instances: every worker faces the same
exponential proof lower bound regardless of random seed. PHP-11-10 times out with
4 workers just as badly as with 1. Cube-and-conquer (C&C) fixes this by genuinely
partitioning the search space — each worker proves a *different* sub-problem UNSAT,
and the results compose into a global UNSAT proof.

Target improvement: PHP-11-10 (currently always times out at 60 s) should solve
within the budget when the search space is split into ≥16 cubes across 4 workers.

---

## Architecture Overview

```
Orchestrator
  │
  ├── CubeQueue  (pending cubes, in-flight map, done list)
  │
  ├── Worker 0 ──solve(cube_0, budget)──► Unsat | Sat | BudgetExceeded
  ├── Worker 1 ──solve(cube_1, budget)──► ...
  ├── Worker 2 ──solve(cube_2, budget)──► ...
  └── Worker 3 ──solve(cube_3, budget)──► ...
        │
        └── on BudgetExceeded: re-split cube → 2 sub-cubes → re-enqueue
```

---

## TODO List

### Phase 1 — Lookahead Cuber

**1.1** Implement pure-CNF lookahead in `crates/rm-sat/src/lookahead.rs` (new file)
- For each unassigned variable probe both polarities via BCP at level 1
- Score = units_forced_positive × units_forced_negative  (March formula)
- Return best-scoring variable as the split candidate
- Detect failed literals during probing (one polarity → immediate conflict → force that variable as level-0 unit)

**1.2** Implement `cube_split(formula, assumptions, depth) -> Vec<Vec<Literal>>`
- Recursively apply 1.1 to depth D, generating up to 2^D cubes
- Prune branches that become UNSAT during lookahead (already refuted; skip)
- Return surviving cubes as `Vec<Vec<Literal>>`

**1.3** Expose `cube_split` from `rm-sat` and wire into `rm-node`, replacing the current shallow `pick_split` in `lookahead.rs`

---

### Phase 2 — Cube Work Queue

**2.1** Add `CubeQueue` to `crates/rm-orchestrator/src/cube_queue.rs` (new file):
```rust
struct CubeQueue {
    pending:   VecDeque<Cube>,
    in_flight: HashMap<WorkerId, Cube>,
    done:      Vec<CubeOutcome>,   // Unsat | Sat(Model)
}
```

**2.2** Add per-cube conflict budget:
- Initial budget: 10 000 conflicts per cube
- On re-split: double the budget for each child cube (exponential backoff)
- Easy cubes finish fast; hard cubes get progressively more budget before re-splitting

**2.3** Dynamic re-splitting logic in orchestrator:
- Worker returns `BudgetExceeded(cube)` → call `cube_split(cube, depth=1)` → enqueue 2 sub-cubes
- Worker returns `Sat(model)` → broadcast stop, return SAT globally
- Worker returns `Unsat` → mark cube done; if all cubes done → return UNSAT globally

---

### Phase 3 — CDCL Worker Integration

**3.1** Add `BudgetExceeded` variant to `SolveResult` in `crates/rm-sat/src/cdcl.rs`:
```rust
pub enum SolveResult {
    Sat(Model),
    Unsat,
    Unknown,
    BudgetExceeded,   // hit conflict budget; orchestrator should re-split
}
```
Current behaviour returns `Unknown` on budget exhaustion — need a distinct signal so the orchestrator knows to re-split rather than retry.

**3.2** Verify cube assumption isolation:
- Cube literals are pushed as assumptions at `base_level`
- Learned clauses exported via AKX must not contain assumption literals (they'd be cube-local, not globally valid)
- Add check in Reasoner export filter: skip clauses whose literals intersect the current cube assumption set

**3.3** Verify assumptions survive restarts correctly (they live at `base_level` — confirm this already works for multi-restart CDCL under assumptions).

---

### Phase 4 — Proof Composition

**4.1** Tag each cube's DRUP proof with its cube context:
- Cube proof covers `C_i ∧ F → ⊥`, i.e., proves `¬C_i` is a consequence of `F`
- Store as `(cube: Vec<Literal>, proof: Vec<Vec<i32>>)`

**4.2** Implement `compose_proofs(cube_proofs)` in `crates/rm-proof/`:
- Emit each cube's proof in sequence
- After all cube proofs: emit the resolution step that combines `¬C_1, ¬C_2, …, ¬C_n`
  into `⊥` (valid because cubes partition the search space exhaustively)
- Output a single valid DRUP file verifiable by `drat-trim`

**4.3** Add `--proof <file>` flag to the CLI `solve` and `benchmark` commands.

---

### Phase 5 — AKX Clause Filtering for Cube Context

**5.1** In Reasoner export: a learned clause is globally valid (safe to share) only if
none of its literals are cube assumption literals. Add this check before `publish`.

**5.2** Use the existing `assumptions` field in `KnowledgeObject`:
- When exporting under cube `C`, set `assumptions = C`
- Import filter at receiver: only apply the clause if the receiver's current cube is
  compatible (same or a sub-cube of the sender's cube)
- This enables full cross-cube clause sharing for cube-independent lemmas

---

### Phase 6 — Orchestrator + CLI Integration

**6.1** Add `CubeAndConquerOrchestrator` to `crates/rm-orchestrator/`:
```
Loop:
  1. Start with CubeQueue containing one empty cube (= full problem)
  2. Assign pending cubes to free workers (up to num_workers in parallel)
  3. On result:
       Sat(model)      → broadcast stop, return SAT
       Unsat           → mark done; if all done → return UNSAT + compose proofs
       BudgetExceeded  → re-split cube into 2, re-enqueue both
  4. Heartbeat monitoring via existing WorkerRecord machinery
```

**6.2** Add `--strategy portfolio|cubeconquer` flag to the CLI.
Default: `portfolio` (current behaviour unchanged).

**6.3** Add to experiment TOML schema:
```toml
[cube_and_conquer]
initial_depth       = 0        # cubing depth before first worker dispatch
initial_budget      = 10000    # conflicts per cube before re-split
max_budget          = 5000000  # cap on budget doubling
```

---

### Phase 7 — Testing

**7.1** Unit test: `cube_split` on a 3-variable formula produces correct non-overlapping
cubes whose union covers the full assignment space.

**7.2** Integration test: `php-5-4` (tiny UNSAT, 20 variables) solves correctly in
C&C mode at depth=2 (4 cubes), each cube quickly UNSAT.

**7.3** Proof correctness test: run the composed DRUP proof for `php-7-6` through
`drat-trim`; must verify cleanly.

**7.4** Regression: all 39 existing unit tests pass; `--strategy portfolio` behaviour
is unchanged.

---

## Effort Estimate

| Phase | Description | Estimate |
|-------|-------------|----------|
| 1 | Lookahead cuber (CNF-level BCP loop) | 3–4 days |
| 2 | Cube queue (data structures) | 1 day |
| 3 | CDCL worker integration | 1 day |
| 4 | Proof composition | 2 days |
| 5 | AKX clause filtering | 1 day |
| 6 | Orchestrator + CLI wiring | 2 days |
| 7 | Testing | 2 days |
| **Total** | | **~12–14 days** |

Highest risk: **Phase 4** (proof composition — silent correctness bugs).
Highest leverage: **Phase 1** (cuber quality determines work balance).

---

## Key Files

| File | Role |
|------|------|
| `crates/rm-sat/src/lookahead.rs` | New: CNF-level lookahead cuber |
| `crates/rm-sat/src/cdcl.rs` | Add `BudgetExceeded` to `SolveResult` |
| `crates/rm-orchestrator/src/cube_queue.rs` | New: cube work queue |
| `crates/rm-orchestrator/src/lib.rs` | New: `CubeAndConquerOrchestrator` |
| `crates/rm-proof/src/` | New: `compose_proofs` |
| `crates/reasonmesh-cli/src/main.rs` | Add `--strategy`, `--proof` flags |
| `crates/rm-node/src/lookahead.rs` | Replace shallow `pick_split` with Phase 1 |
