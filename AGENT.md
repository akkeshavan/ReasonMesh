# ReasonMesh Agent Status — 2026-10-20

## Repository

Public at https://github.com/akkeshavan/ReasonMesh — v0.1.0 in progress.

---

## Current State

### What is working

| Component | Status |
|---|---|
| CDCL SAT core (`rm-sat`) | Production quality — 71 tests passing |
| Parallel portfolio with AKX clause sharing | Working — 4-thread within 1.2× of Kissat/Z3 on SATLIB |
| QF_BV (Tseitin bit-blasting) | Working |
| QF_IDL / QF_RDL (Bellman-Ford) | Working |
| QF_UF (e-graph congruence closure) | Working — 191/200 SMTLIB correct |
| QF_UFIDL (Nelson-Oppen EUF+DL) | Partial — 87/200, 57% timeout rate |
| QF_LIA / QF_UFLIA (Simplex) | Partial — ~86/200, 57% timeout rate; 0 wrong answers; all unit tests passing |
| TCP cluster transport (`rm-cluster`) | Working — correctness tests pass |
| Benchmark harness (`rm-bench`) | Working — checkpoint/resume, baseline comparison |
| Proof certificates (DRUP, `rm-proof`) | Working for SAT |

### Benchmark summary (latest runs)

**SATLIB (807 problems, 4 threads, 300 s timeout):**
796/807 solved, PAR-2 = 7 647 s (Kissat: 6 373 s, Z3: 6 401 s). No wrong answers.
See `Benchmarks.md` for per-category breakdown.

**SMTLIB QF_UF/QF_UFIDL/QF_UFLIA (600 problems, 1 thread, 60 s timeout):**
S33 (2026-10-20): fixed 3 wrong answers (xs_29_29, xs_25_25, vhard4) vs S31+S32; 0 wrong answers total. Full run pending.
Previous run (30 s timeout): 364/600 correct, PAR-2 = 16 310 s (Z3: 9 549 s), 0 wrong.
See `Benchmarks.md` for details.

---

## Recent Changes

### S33 (2026-10-20)

**S26 soundness filter (`mk_safe_conflict_simplex`):**
S26 incremental congruence probe now uses `mk_safe_conflict_simplex` instead of `mk_conflict_simplex`. Rejects conflict clauses whose core contains a negative-polarity raw literal (tightened integer bound from `theory_propagate`). Such clauses are branch-local — valid in the current CDCL branch but not globally — so adding them to the permanent SAT database is unsound. This fixes false-SAT on vhard4 and removes false-UNSAT on xs_29_29 and xs_25_25.

**S26 bound fix:**
S26 probe assertions now use `le_bound + 1` and `ge_bound - 1` (extracted from the actual atom) instead of hardcoded ±1. Correct for all Ackermann diff slacks (which always have bound 0, so no change there) and future constant-bound scenarios.

**S26 user-var guard:**
When neither le_sat nor ge_sat is TRUE, the probe now skips pairs where either arg variable is a user-declared variable (in `var_ids`). User vars are freely assigned by Simplex to their lower bounds so model equality is coincidental, not structural. Non-user vars (UF result vars, constant-pinned slacks) have constrained model values and can generate sound transitivity lemmas.

### S31+S32 (2026-10-17, commit 6e75e4ff)

**S32 — dual Not(ArithCmp) encoding:**
`¬(ArithCmp)` in `encode_bool` now encodes the dual comparison as a fresh positive atom instead of a negated literal. e.g. `¬(x ≤ k)` → `Lower(x, k+1)`. This means `theory_propagate` asserts the tightened bound when the literal is TRUE (rather than silently skipping it as a FALSE atom). Fixed false-SAT on TwoSquares 602046.

**S31 — De Morgan Not(Or) expansion:**
`¬(A ∨ B ∨ …)` is now encoded as a Tseitin AND of `(¬A, ¬B, …)`. Combined with S32, this pushes negation through disjunctions containing `ArithCmp` so each `¬(ArithCmp)` sub-expression becomes a positive bound atom. Also adds double-negation elimination `¬(¬x) → x`. Fixed false-SAT on TwoSquares 602059 and 606727.

### S29+S30 (2026-09-30, commit 6bfdfe2a)

**Selective integer tightening in `theory_propagate`:**
Restored integer tightening `¬(x ≤ k) → x ≥ k+1` for plain arithmetic comparison atoms, but skip it for atoms in `ackermann_le_ge_atoms` (the le/ge components of Tseitin AND gates for Ackermann/ITE equality). Fixed the `hash_sat_06_03` false-UNSAT regression while preserving TwoSquares soundness.

**`encode_var_eq` atom-sharing:**
Reuses existing `arith_atom_cache` atoms when encoding Ackermann arg equalities, allowing BCP to propagate congruence constraints. Fixed the `uf_congruence_unsat` and `uf_constant_offset_arg_unsat` unit tests.

---

## Open Issues

### 1. QF_UFIDL and QF_UFLIA timeout rate (~57%)

Nelson-Oppen T-propagation between EUF and DL is incomplete. The CDCL(T) loop exits too early
on disjunctive instances because the EUF theory does not propagate equalities back to the DL
solver proactively. Fixing T-propagation completeness is the highest-ROI improvement for
QF_UFIDL.

---

## What Needs to Be Done (ordered by priority)

- [ ] Improve QF_UFIDL T-propagation (complete Nelson-Oppen EUF↔DL propagation)
- [ ] Parallel CDCL(T): share theory lemmas (not just SAT clauses) over AKX bus
- [ ] Cube-and-conquer for SMT instances (currently SAT only)
- [ ] DRUP proof certificates for SMT logics
- [ ] Metal GPU WalkSAT kernel (stub exists at `crates/rm-gpu/src/lib.rs`, kernel not written)
- [ ] CI on Linux and Windows (currently macOS-only)
- [ ] Publish to crates.io
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
