# ReasonMesh Agent Status — 2026-09-09

## What We're Working On

Closing the performance gap between ReasonMesh CDCL solver and CaDiCaL on the g2 benchmark (16 problems: 7 PHP pigeonhole UNSAT + 9 random 3-SAT).

**Baseline (v4 PAR-2): 1835.8s**

The gap decomposes into:
- 1.2× single-thread BCP throughput (partially closed: 1.99→2.63 Mprop/s early)
- 2.4× watch-list bloat (core problem)
- ~2× multi-worker overhead

---

## Current Implementation State

### What's been implemented (in code, tests passing)

1. **Header bit layout change** (`crates/rm-sat/src/clause.rs`):
   - Old: LBD in bits 2-15 (14 bits, mask 0x3FFF)
   - New: LBD in bits 2-14 (13 bits, mask 0x1FFF), bit 15 = `used_since_reduce`
   - Max LBD = 8191, never reached in practice
   - `is_used()`, `mark_used()` methods added
   - `reduce_learned()` now takes `used: bool` as 5th closure parameter
   - Tier-2 survivors (LBD 3-6) have used bit cleared at each reduce

2. **`mark_used` in conflict analysis** (`crates/rm-sat/src/cdcl.rs`, `process_reason_into`):
   - Every learned clause used as a reason in conflict analysis gets `mark_used` called

3. **New clause initialization** (`clause.rs` `add()`):
   - Tier-2 learned clauses (LBD 3-6) start with `used = true` (matching CaDiCaL)
   - This gives one free reduce round before the clause must prove its value

4. **Current deletion predicate** (mode-adaptive, `cdcl.rs` `maybe_reduce_db`):
   ```rust
   let in_stable = self.mode == SolverMode::Stable;
   self.db.reduce_learned(|cr, lbd, activity, lit0, used| {
       lbd > 2
           && self.assignment.reason_of(lit0.var()) != cr.0
           && (lbd > 6
               || if in_stable { !used } else { activity < 1e-4 })
   });
   ```
   - Focus mode: activity-based (v4-style, preserves SAT phase-guiding clauses)
   - Stable mode: used-bit (CaDiCaL-style, keeps watch lists tight for UNSAT)

### All 39 tests pass.

---

## Benchmark Results So Far

### Quick 5-problem results (experiments/quick-check.toml):

| problem | v4 (baseline) | v8 (used=true init) | v11 (mode-adaptive) |
|---------|--------------|---------------------|---------------------|
| php-10-9 (UNSAT) | 7.818s | 8.146s | 13.128s |
| r3sat-150-r425 (SAT) | 0.048s | 0.120s | 0.154s |
| r3sat-238-1 (SAT) | 0.101s | 0.156s | 0.113s |
| r3sat-238-2 (UNSAT) | 10.718s | 4.933s | 5.164s |
| r3sat-240-r425 (UNSAT) | 14.885s | 7.755s | 7.663s |

### Full 16-problem PAR-2 (experiments/g2-vs-z3.toml):

| version | PAR-2 | vs v4 |
|---------|-------|-------|
| v4 (baseline, activity only) | 1835.8s | — |
| v7 (used=false init BUG) | 1832.8s | -3.1s |
| v8 (used=true init) | 1837.8s | +2.0s |

**The full v11 benchmark was interrupted.**

---

## The Core Problem We're Debugging

**Tension between SAT and UNSAT performance:**

- **UNSAT benefit**: used-bit deletion keeps watch lists smaller → much faster BCP → r3sat-238-2 improves from 10.7s to 4.9s
- **SAT harm**: used-bit deletion removes phase-guiding clauses that prevent conflicts (they participate in BCP propagation but not conflict analysis, so never get `mark_used`)
- **PHP harm**: noisy due to 4-worker non-determinism; ranges from 7.8s to 15s across runs

**Why mode-adaptive (v11) is also struggling:**
- PHP-10-9 is UNSAT and spends time in Stable mode (should benefit) but results are noisy
- r3sat-150 (SAT, 15285 conflicts) still regresses because it may hit reduce in Stable mode before solving
- 4-worker non-determinism makes it hard to isolate the signal

---

## What To Try Next

### Option A: Single-thread baseline first
Run `cargo run --release -p reasonmesh-cli -- solve benchmarks/g1/php-10-9.cnf` with 1 worker to eliminate multi-worker noise from the PHP numbers.

### Option B: Best-phase / target-phase tracking (technique #3)
For SAT instances specifically, implementing "target phase" from Kissat:
- Track `best_trail: Vec<bool>` — snapshot of polarity when trail reaches new maximum
- On Stable→Focus transition: reset saved phases to `best_trail`
- This is the primary fix for SAT instance regressions (r3sat-238-1, r3sat-150)

### Option C: Fixed-interval reduction (technique #2)
Replace `learnt_count > limit` trigger with conflict-interval trigger (every N conflicts, grow N by 1.1×). This decouples reduce frequency from clause learning rate and gives more stable intervals.

### Option D: Revert used-bit for now, only keep the layout+mark_used infrastructure
Keep the bit-layout change and `mark_used` infrastructure for future use, but revert the deletion predicate to pure activity-based (v4 behavior). The infrastructure is correct and tested; the deletion strategy can be refined with best-phase + fixed-interval first.

---

## Key Files

- `crates/rm-sat/src/clause.rs` — Header bit layout, `is_used`, `mark_used`, `reduce_learned`
- `crates/rm-sat/src/cdcl.rs` — `maybe_reduce_db`, `process_reason_into`, `add_learned_clause`
- `experiments/g2-vs-z3.toml` — 16-problem benchmark manifest
- `experiments/quick-check.toml` — 5-problem quick benchmark (created this session)
- `benchmarks/results/g2/g2-vs-z3-v4.json` — v4 baseline results (reference)
- Scratchpad: `/private/tmp/claude-501/-Users-anand-air-projects-ReasonMesh/f21a5d31-fd95-4ed9-b05d-4395be04206f/scratchpad/`
  - `v7.json` — v7 full benchmark (used=false bug, PAR-2 1832.8s)
  - `v8-full.json` — v8 full benchmark (used=true init, PAR-2 1837.8s)
  - `v8-quick.json`, `v9-quick.json`, `v10-quick.json`, `v11-quick.json` — quick runs

---

## Recommendation for Tomorrow

Start with **Option D** (revert deletion predicate to v4 activity-based), commit the infrastructure changes (bit layout + mark_used + used=true init) as a clean foundation, then implement best-phase tracking (Option B) which is the higher-ROI technique for SAT instances. The used-bit deletion can be re-introduced on top once best-phase is working.

Commit message for current infrastructure: "Add used_since_reduce bit to clause header for CaDiCaL-style tier-2 tracking"
