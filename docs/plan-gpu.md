# GPU Acceleration Implementation Plan

## Motivation

The CDCL core (BCP, conflict analysis) is inherently sequential and cannot be
GPU-accelerated. But three components are embarrassingly parallel and bottleneck
solver quality on hard instances:

| Component | Current | GPU target |
|-----------|---------|------------|
| `walk_phase` | 1 sequential WalkSAT run, n×16 steps | 10 000 parallel trajectories, best polarity returned |
| Lookahead cuber | Score variables one at a time (C&C Phase 1) | Score all n variables simultaneously in one kernel |
| Inprocessing (vivify/subsume) | Sequential candidate loop | Batch candidate checks in parallel |

Expected impact: SAT instances (where phase guidance matters) should improve
significantly. UNSAT instances are unaffected by walk but benefit from faster
cube generation in C&C mode.

---

## Architecture

```
rm-sat (CdclSolver)
    │
    └── GpuAccelerator trait (rm-gpu)
            │
            ├── MetalBackend  (rm-gpu / feature "metal")   ← Apple Silicon, local dev
            └── CudaBackend   (rm-gpu-cuda)                ← NVIDIA, cloud benchmarking
```

`rm-gpu` defines the backend-agnostic trait. Both backends implement it.
The solver holds an `Option<Box<dyn GpuAccelerator>>` — if None, falls back
to the existing CPU implementation. No behaviour change when GPU is absent.

---

## TODO List

### Phase G1 — Backend-Agnostic Trait (`rm-gpu`)

**G1.1** Define the `GpuAccelerator` trait in `crates/rm-gpu/src/lib.rs`:

```rust
pub trait GpuAccelerator: Send + Sync {
    /// Run `num_trajectories` independent WalkSAT runs on the GPU.
    /// Returns the polarity assignment that satisfied the most clauses.
    fn walk(
        &self,
        clauses: &[GpuClause],      // flat clause list (literals as i32)
        num_vars: u32,
        seed: u64,
        num_trajectories: u32,      // typically 10_000
        steps_per_trajectory: u32,  // typically num_vars * 4
    ) -> Vec<bool>;                 // best polarity[0..=num_vars]

    /// Score all unassigned variables for lookahead cubing.
    /// Returns lookahead_score[var] = forced_pos * forced_neg.
    fn lookahead_scores(
        &self,
        clauses: &[GpuClause],
        num_vars: u32,
        assigned: &[Option<bool>],  // current partial assignment
    ) -> Vec<u64>;                  // score per variable (0 = skip)

    /// Device name / description for logging.
    fn device_name(&self) -> &str;
}

/// Clause representation for GPU transfer: literals as signed ints (DIMACS style).
pub struct GpuClause {
    pub lits: Vec<i32>,
}
```

**G1.2** Add `CpuFallback` implementing `GpuAccelerator` using the existing
`walk_phase` and lookahead BCP. This is the reference implementation used in
correctness tests.

**G1.3** Add `GpuClause` serialisation helpers: convert `ClauseArena` slices into
the flat `Vec<GpuClause>` format needed for GPU transfer. This is called once per
stable restart, not per conflict, so transfer cost is amortised.

---

### Phase G2 — Metal Backend (Apple Silicon, local dev/testing)

**G2.1** Add `features = ["metal"]` to `rm-gpu/Cargo.toml`. Add dependency on
`metal` crate (Apple's Metal bindings for Rust).

**G2.2** Implement `MetalBackend::walk` as a Metal compute kernel:

- Kernel: each thread = one WalkSAT trajectory. Threads share read-only clause
  buffer (Metal device buffer). Each thread has its own private assignment array.
- Steps: initialise assignment from `seed ^ thread_id`, run `steps_per_trajectory`
  greedy-flip steps, write `(thread_id, sat_count)` to output buffer.
- Host side: launch `num_trajectories` threads, read back output, pick best
  `thread_id`, read its assignment.

Walk kernel pseudocode (Metal Shading Language):
```metal
kernel void walksat(
    device const int* clauses   [[ buffer(0) ]],
    device const uint* offsets  [[ buffer(1) ]],  // clause start indices
    device uint* best_sat_count [[ buffer(2) ]],
    device uint* best_thread_id [[ buffer(3) ]],
    device const WalkParams* p  [[ buffer(4) ]],
    uint tid [[ thread_position_in_grid ]]
) {
    // initialise private assignment from (seed ^ tid)
    // run p->steps greedy flips
    // atomic_max on best_sat_count, store tid
}
```

**G2.3** Implement `MetalBackend::lookahead_scores`:
- Kernel: each thread = one unassigned variable. Probes positive and negative
  at level 1 using a lightweight BCP simulation (no watch lists — use occurrence
  lists pre-built on host). Writes `forced_pos * forced_neg` to output.

**G2.4** Wire `MetalBackend` into `CdclSolver::walk_phase`:
- If `self.gpu.is_some()`: build `GpuClause` list, call `gpu.walk(...)`,
  write returned polarity back to `self.polarity` (only if improvement, same
  guard as existing CPU path).
- Else: existing sequential CPU walk (unchanged).

**G2.5** Construction: `CdclSolver::new_with_gpu(num_vars, gpu: Box<dyn GpuAccelerator>)`
alongside the existing `new(num_vars)`. The `reasonmesh-cli` can try to
initialise a `MetalBackend`, fall back silently to CPU if Metal is unavailable.

---

### Phase G3 — CUDA Backend (`rm-gpu-cuda`, cloud benchmarking)

**G3.1** Add dependency on `cudarc` crate (safe Rust CUDA bindings, no unsafe
FFI needed for kernel launch).

**G3.2** Write WalkSAT kernel in CUDA C (`src/walksat.cu`):
- Same logic as Metal kernel — one thread per trajectory
- Use `__shared__` memory for the clause literal buffer if it fits (< 48 KB for
  typical problem sizes)
- Compile via `build.rs` using `nvcc`; embed PTX in the binary

**G3.3** Implement `CudaBackend::walk` and `CudaBackend::lookahead_scores`
mirroring the Metal API. Copy clause data to device once per walk call via
`cudarc` device buffers.

**G3.4** Add `build.rs` that detects CUDA toolkit presence and skips compilation
gracefully if absent (so the crate builds on non-CUDA machines as a no-op).

---

### Phase G4 — GPU Preprocessing (lower priority)

**G4.1** GPU-accelerated vivification candidate scoring:
- For each candidate clause, compute a "vivification score" = number of its
  literals that are forced under current assignment. GPU kernel: one thread
  per candidate clause, reads the current partial assignment, writes score.
- Use to prioritise the `MAX_VIVIFY` candidates instead of the current LBD sort.

**G4.2** GPU subsumption pre-filter:
- Compute clause signature (bitset of variable indices mod 64) on GPU for all
  clause pairs. Two clauses can only subsume each other if `sig_A & sig_B == sig_A`.
  This pre-filter reduces the O(n²) subsumption check to O(candidates).

These are lower-priority; G1–G3 deliver the walk improvement which is the main result.

---

### Phase G5 — Integration and Configuration

**G5.1** Add to experiment TOML schema:
```toml
[gpu]
enabled = true
backend = "metal"          # "metal" | "cuda" | "cpu"
walk_trajectories = 10000
walk_steps_per_var = 4     # steps = num_vars * this
```

**G5.2** Add `--gpu / --no-gpu` flag to CLI `solve` and `benchmark` commands.

**G5.3** Log GPU device name and trajectory count at solver startup.

---

### Phase G6 — Testing

**G6.1** Correctness test — `CpuFallback` vs `MetalBackend` on the same formula
and seed must produce identical `sat_count` (not necessarily identical polarity,
since tie-breaking may differ, but the same best score):
```rust
let cpu_score = cpu_fallback.walk(&clauses, n, seed, 1, n*16).sat_count();
let gpu_score = metal.walk(&clauses, n, seed, 10_000, n*4).sat_count();
assert!(gpu_score >= cpu_score);  // GPU explores more, should be ≥
```

**G6.2** Lookahead score correctness: `MetalBackend::lookahead_scores` vs
`CpuFallback::lookahead_scores` on 20 random formulas. Scores must match exactly
(BCP is deterministic).

**G6.3** Performance test (Metal, local): measure `walk_phase` wall time with
GPU vs CPU on `r3sat-240-r425`. Expect ≥10× speedup for the walk itself.

**G6.4** Solver benchmark (Metal, local): run g2 quick-check (5 problems) with
`--gpu metal` vs `--no-gpu`. SAT instances should improve; UNSAT should be neutral.

**G6.5** Cloud benchmark (CUDA, AWS g4dn.xlarge, $0.53/hr spot):
- Cross-compile: `cargo build --release --target x86_64-unknown-linux-gnu --features cuda`
- `scp` binary + CNF files to instance
- Run full 16-problem g2 suite, compare PAR-2 vs M7 (CPU only)

**G6.6** Regression: all 39 existing unit tests pass with `--no-gpu`. GPU path
must be a strict opt-in — no behaviour change when disabled.

---

## Effort Estimate

| Phase | Description | Estimate |
|-------|-------------|----------|
| G1 | Trait + CPU fallback | 1 day |
| G2 | Metal backend (walk + lookahead) | 4–5 days |
| G3 | CUDA backend | 3–4 days |
| G4 | GPU preprocessing | 2 days |
| G5 | Config / CLI integration | 1 day |
| G6 | Testing | 2 days |
| **Total** | | **~13–15 days** |

Metal (G2) should be done before CUDA (G3) — same kernel logic, easier to
debug locally without a cloud round-trip. CUDA is a straight port once Metal works.

---

## Key Files

| File | Role |
|------|------|
| `crates/rm-gpu/src/lib.rs` | `GpuAccelerator` trait + `CpuFallback` + `GpuClause` |
| `crates/rm-gpu/src/metal.rs` | Metal backend (new) |
| `crates/rm-gpu/src/metal/walksat.metal` | Metal Shading Language kernel |
| `crates/rm-gpu/src/metal/lookahead.metal` | Metal lookahead kernel |
| `crates/rm-gpu-cuda/src/lib.rs` | CUDA backend |
| `crates/rm-gpu-cuda/src/walksat.cu` | CUDA WalkSAT kernel |
| `crates/rm-gpu-cuda/build.rs` | nvcc compilation + graceful no-op if absent |
| `crates/rm-sat/src/cdcl.rs` | Add `gpu: Option<Box<dyn GpuAccelerator>>` field |
| `crates/reasonmesh-cli/src/main.rs` | `--gpu` flag, Metal/CUDA init |

---

## Interaction with Cube-and-Conquer Plan

GPU lookahead (G2.3 / G3) directly accelerates C&C Phase 1 (the cuber). Once
both plans are implemented, the full pipeline is:

```
GPU lookahead → fast cube generation (C&C)
     │
     └── each cube → CPU CDCL worker + GPU walk_phase guidance
```

This is the target architecture for the paper's scaling experiments.
