# ReasonMesh — Benchmark Results

Results from the most recent completed runs. All times are wall-clock seconds unless noted.
Regenerate with `reasonmesh benchmark <manifest>` — raw JSON lives in `results/`.

---

## SATLIB — random and structured SAT (807 problems)

**Manifest:** `experiments/satlib-fair-4t.toml`
**Config:** 4 workers, AKX clause sharing, 300 s timeout
**Baselines:** Kissat 3.1 (1 thread), Z3 4.12 (4 threads)

### Per-category results

| Category | Problems | RM solved | Timeouts | RM avg (ms) |
|---|---|---|---|---|
| uf50 | 50 | 50 | 0 | 2 |
| uuf50 | 50 | 50 | 0 | 1 |
| uf100 | 50 | 50 | 0 | 6 |
| uuf100 | 50 | 50 | 0 | 12 |
| uf150 | 50 | 50 | 0 | 34 |
| uuf150 | 50 | 50 | 0 | 259 |
| uf200 | 50 | 50 | 0 | 263 |
| uuf200 | 50 | 50 | 0 | 965 |
| uf250 | 50 | 50 | 0 | 1 429 |
| uuf250 | 50 | 49 | 1 | 19 090 |
| flat50–flat200 | 200 | 200 | 0 | ≤13 |
| aim | 72 | 72 | 0 | 1 |
| phole (hole6–hole10) | 5 | 5 | 0 | <1 |
| parity | 30 | 20 | 10 | 20 145 |
| **Total** | **807** | **796** | **11** | — |

### PAR-2 comparison (300 s penalty)

| Solver | Solved | PAR-2 |
|---|---|---|
| ReasonMesh 0.1.0 (4t) | 796 | 7 647 s |
| Kissat 3.1 (1t) | 797 | 6 373 s |
| Z3 4.12 (4t) | 797 | 6 401 s |

ReasonMesh is within 1.2× of Kissat and Z3 on PAR-2. The gap is entirely in the 11 timeout instances (10 parity, 1 uuf250). All 796 solved instances have correct answers.

---

## SMTLIB — QF_UF / QF_UFIDL / QF_UFLIA (600 problems)

**Manifest:** `experiments/smtlib-uflia-run17.toml`
**Config:** 1 worker, 30 s timeout
**Baseline:** Z3 4.12 (1 thread)
**Source:** Official SMTLIB 2023 benchmark suite, 200 problems per logic

### Per-logic results

| Logic | RM correct | RM timeout | RM wrong | RM avg (ms) | Z3 solved | Z3 avg (ms) |
|---|---|---|---|---|---|---|
| QF_UF | 191 / 200 | 9 | 0 | 4 596 | 200 / 200 | 459 |
| QF_UFIDL | 87 / 200 | 113 | 0 | 38 557 | 184 / 200 | 9 948 |
| QF_UFLIA | 86 / 200 | 114 | 0 | 38 404 | 174 / 200 | 29 349 |
| **Total** | **364 / 600** | **236** | **0** | — | **558 / 600** | — |

### PAR-2 comparison (30 s penalty)

| Solver | Solved | PAR-2 |
|---|---|---|
| ReasonMesh 0.1.0 (1t) | 364 | 16 310 s |
| Z3 4.12 (1t) | 558 | 9 549 s |
| RM / Z3 ratio | — | 1.71× |

**QF_UF** is close to Z3 (191/200 vs 200/200). **QF_UFIDL** and **QF_UFLIA** are the active improvement areas — both have ~57% timeout rates. No wrong answers on any logic.

---

## Notes

- All SATLIB runs used the 4-thread portfolio with AKX clause sharing enabled. Single-thread performance is roughly 1.5× slower on the uf250/uuf250 category.
- SMTLIB runs used a single thread with a 30 s wall-clock timeout. The 30 s budget is tight for QF_UFIDL and QF_UFLIA; the timeout rate drops significantly at 60 s.
- PAR-2 penalises each timeout at 2× the time limit. Lower is better.
- Raw JSON results are in `results/` (gitignored, regenerate locally).
- Experiment manifests are in `experiments/`.
