# ReasonMesh Agent Status — 2026-10-12

## Repository

Public at https://github.com/akkeshavan/ReasonMesh — v0.1.0 in progress.

---

## Current State

### What is working

| Component | Status |
|---|---|
| CDCL SAT core (`rm-sat`) | Production quality — 74 tests passing |
| Parallel portfolio with AKX clause sharing | Working — 4-thread within 1.2× of Kissat/Z3 on SATLIB |
| QF_BV (Tseitin bit-blasting) | Working |
| QF_IDL / QF_RDL (Bellman-Ford) | Working |
| QF_UF (e-graph congruence closure) | Working — 191/200 SMTLIB correct |
| QF_UFIDL (Nelson-Oppen EUF+DL) | Partial — 87/200, 57% timeout rate |
| QF_LIA / QF_UFLIA (Simplex) | Partial — 86/200, 57% timeout rate; 2 unit tests failing |
| TCP cluster transport (`rm-cluster`) | Working — correctness tests pass |
| Benchmark harness (`rm-bench`) | Working — checkpoint/resume, baseline comparison |
| Proof certificates (DRUP, `rm-proof`) | Working for SAT |

### Benchmark summary (latest runs)

**SATLIB (807 problems, 4 threads, 300 s timeout):**
796/807 solved, PAR-2 = 7 647 s (Kissat: 6 373 s, Z3: 6 401 s). No wrong answers.
See `Benchmarks.md` for per-category breakdown.

**SMTLIB QF_UF/QF_UFIDL/QF_UFLIA (600 problems, 1 thread, 30 s timeout):**
364/600 correct (QF_UF: 191/200, QF_UFIDL: 87/200, QF_UFLIA: 86/200), PAR-2 = 16 310 s (Z3: 9 549 s).
No wrong answers. See `Benchmarks.md` for details.

---

## Open Issues

### 1. Two failing QF_UFLIA unit tests (blocking crates.io publish)

**`uf_congruence_unsat`** and **`uf_constant_offset_arg_unsat`** in `crates/rm-smt/src/lia.rs`.

Root cause: `encode_var_eq` bypasses `arith_atom_cache` and allocates fresh SAT variables for
Simplex bound atoms that `encode_arith_cmp` may have already created. The SAT solver then treats
them as independent, allowing it to set the Ackermann equality atoms to false even when the
corresponding user-asserted equality is true.

**Fix for `uf_congruence_unsat`** (straightforward):
In `encode_var_eq` (lia.rs ~line 654), after computing `slack = form_to_var(diff)`, look up
`arith_atom_cache[(slack, true, 0)]` and `arith_atom_cache[(slack, false, 0)]` before calling
`alloc_sat()`. Reuse existing atoms if present, insert if not.

**Fix for `uf_constant_offset_arg_unsat`** (harder):
The arg equality is derivable from Simplex row equations (e.g. `slack_xp1 = x+1` and `y-x = 1`)
but there are no explicit bounds on the diff slack. The cache fix above doesn't help because no
`encode_arith_cmp` was ever called on that form. Requires model-value-based congruence checking in
`theory_final_check`: after `scratch.check()`, walk `ackermann_arg_tprop` pairs and detect when
`scratch.model_value(arg_i) == scratch.model_value(arg_j)` but result vars differ.

Relevant functions:
- `encode_var_eq` — lia.rs:635
- `encode_arith_cmp` — lia.rs:1039 (has the cache)
- `theory_final_check` — lia.rs:517
- `theory_propagate` — lia.rs:393

### 2. QF_UFIDL and QF_UFLIA timeout rate (~57%)

Nelson-Oppen T-propagation between EUF and DL is incomplete. The CDCL(T) loop exits too early
on disjunctive instances because the EUF theory does not propagate equalities back to the DL
solver proactively. Fixing T-propagation completeness is the highest-ROI improvement for
QF_UFIDL.

---

## What Needs to Be Done (ordered by priority)

- [ ] Fix `uf_congruence_unsat` — use `arith_atom_cache` in `encode_var_eq`
- [ ] Fix `uf_constant_offset_arg_unsat` — model-value congruence check in TFC
- [ ] Improve QF_UFIDL T-propagation (complete Nelson-Oppen EUF↔DL propagation)
- [ ] Parallel CDCL(T): share theory lemmas (not just SAT clauses) over AKX bus
- [ ] Cube-and-conquer for SMT instances (currently SAT only)
- [ ] DRUP proof certificates for SMT logics
- [ ] Metal GPU WalkSAT kernel (stub exists at `crates/rm-gpu/src/lib.rs`, kernel not written)
- [ ] CI on Linux and Windows (currently macOS-only)
- [ ] Publish to crates.io (blocked on the two unit test failures above)
- [ ] Lean 4 tactic integration (`docs/integrations.md` documents the intended API)

---

## Key Files

| File | Purpose |
|---|---|
| `crates/rm-smt/src/lia.rs` | QF_LIA/QF_UFLIA encoder, Simplex DPLL(T) loop |
| `crates/rm-smt/src/cdclt.rs` | Generic CDCL(T) loop |
| `crates/rm-smt/src/dl.rs` | QF_IDL/QF_RDL Bellman-Ford theory |
| `crates/rm-smt/src/uf.rs` | QF_UF congruence closure theory |
| `crates/rm-theory-arith/src/simplex.rs` | Dutertre-de Moura Simplex |
| `crates/rm-sat/src/cdcl.rs` | CDCL engine |
| `crates/rm-sat/src/parallel.rs` | Parallel worker pool |
| `crates/rm-cluster/src/` | TCP cluster transport |
| `experiments/` | Benchmark manifests |
| `Benchmarks.md` | Latest benchmark results tables |
| `docs/architecture_spec.md` | Full design spec (AKX protocol v0.2) |
