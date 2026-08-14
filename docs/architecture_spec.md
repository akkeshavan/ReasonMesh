# ReasonMesh — Architecture and Research Specification v0.2

**A Massively Parallel SMT Solver Based on Asynchronous Knowledge Exchange**

> **Working research question:** Can SMT solving be organized around
> asynchronous exchange of independently derived, assumption-scoped logical
> knowledge rather than globally coordinated CDCL(T) search — and if so,
> which knowledge kinds and routing policies drive that benefit?

*Specification v0.2 — 14 August 2026*  
*Implementation language: Rust*

---

## Changelog from v0.1

| Issue | Resolution in this version |
|---|---|
| Assumption-scoped import checking unspecified | §7.3 now gives a formal import predicate and an efficient checking protocol |
| UNSAT completeness under asynchrony unproven | §8.4 gives a formal completeness argument per parallelism mode |
| Nelson-Oppen / asynchrony conflict unacknowledged | §11.1 documents the tension and gives the resolution strategy |
| `KnowledgeBus::publish` returned void | Now returns `Result<PublishHandle, BusError>`; §12.1 adds back-pressure |
| `WorkUnit` had no cancellation token | `WorkUnit` now carries `shutdown: Arc<AtomicBool>` |
| `ReasonerEvent`, `Capabilities`, `Checkpoint` undefined | All three types are now fully sketched in §7.2 |
| No `Result` in Reasoner trait methods | All trait methods now return `Result` |
| Orchestrator SPOF with no failover protocol | §13.4 adds primary/standby orchestrator protocol |
| Knowledge bus had no eviction policy | §12.3 defines eviction priority and buffer limits |
| Novelty boundary vs. Mallob not formally precise | §4.4 gives a crisp three-axis formal distinction |
| SAT-first pivot risk to SMT not acknowledged | §18 adds an explicit pivot risk gate (G0) |
| Cube-and-Conquer missing from related work | Added to §23 as reference [9] |
| Synthetic benchmark design bias | §16.1 makes external benchmarks primary; synthetics ablation-only |
| Section 21 list numbering wrong (12–21) | Fixed to 1–10 |
| Architecture diagram missing from export | §6 now described textually; diagram lives in docs/figures/ |

---

# 1. Executive Summary

ReasonMesh is a research and engineering project to build a production-grade,
massively parallel Satisfiability Modulo Theories (SMT) solver whose primary
architectural abstraction is a mesh of heterogeneous reasoners exchanging
independently derived, assumption-scoped logical knowledge. The system is
intended to scale from a deterministic single-process configuration to
multi-core machines, multi-GPU servers, and distributed CPU/GPU clusters.

The project deliberately does not treat parallelism as an optional optimization
layer bolted onto a conventional CDCL(T) implementation. Instead, concurrency,
decomposition, stale-but-sound knowledge, hierarchy, communication cost,
accelerator specialization, failure recovery, and proof provenance are
first-class design concerns.

The implementation has two equally important outputs:

- A serious open research solver capable of solving SMT-LIB workloads across
  heterogeneous compute resources.
- An evidence base for a journal paper evaluating whether asynchronous
  knowledge exchange can serve as a scalable organizing principle for SMT
  solving.

> **Key discipline:** The implementation is an experiment. The paper must not
> assume the hypothesis is true. The architecture, telemetry, and benchmark
> plan are designed so that failure to scale is measurable and scientifically
> useful.

---

# 2. Project Name

**ReasonMesh** is the project name. "Reason" describes the function; "Mesh"
captures the absence of a single mandatory reasoning path and the ability of
heterogeneous workers to exchange useful consequences.

| Name | Role |
|---|---|
| ReasonMesh | Project name. Clear, memorable, architecture-neutral. |
| AKX | Name of the Asynchronous Knowledge Exchange protocol inside ReasonMesh. |
| AKX-SMT | Good paper/system name, but too implementation-specific for the project. |

---

# 3. Goals and Success Criteria

## 3.1 Primary goals

- Build a sound, high-performance SMT solver in Rust with a clean, testable
  core and SMT-LIB 2.7 interoperability.
- Scale search and theory reasoning across tens to thousands of CPU workers
  without requiring globally synchronized CDCL(T) state.
- Exploit GPUs for workloads whose structure benefits from massive
  SIMD/SIMT parallelism rather than forcing sequential CDCL control flow
  onto a GPU.
- Define a transport-independent AKX protocol for exchanging learned clauses,
  theory lemmas, bounds, conflicts, cubes, model information, and
  proof/certificate fragments.
- Support heterogeneous reasoners: CPU CDCL(T), local search, GPU
  bit-vector/circuit evaluation, theory-specific engines, partitioners, and
  proof checkers.
- Make every optimization measurable through deterministic replay, rich
  telemetry, and reproducible benchmark manifests.
- Produce a research artifact and experimental results strong enough for
  peer-reviewed publication.

## 3.2 Non-goals for the first research release

- Immediate feature parity with Z3 or cvc5 across every SMT-LIB theory.
- GPU acceleration as a marketing checkbox; GPU code must improve end-to-end
  solving on defined workloads or it is dropped.
- A single global clause database or full broadcast of all learned information.
- Global locks or barriers in the normal reasoning path.
- Accepting "SAT" or "UNSAT" without independent validation/certificate checks.
- Premature support for quantifiers, strings, floating point, or nonlinear
  combinations before the scalable core is validated.

---

# 4. Research Thesis

## 4.1 Main research question

> Can SMT solving be organized around asynchronous exchange of independently
> derived, assumption-scoped logical knowledge rather than globally coordinated
> CDCL(T) search — and if so, which knowledge kinds and routing policies drive
> that benefit?

## 4.2 Testable hypothesis

A decentralized SMT architecture in which heterogeneous reasoners
asynchronously exchange logically valid, assumption-scoped knowledge can
achieve better scaling on sufficiently difficult workloads than sequential
solving and conventional fixed-size portfolios, while preserving soundness and
providing a practical route to completeness and proof reconstruction.

## 4.3 What would count as a contribution

- A formal knowledge model that permits independently derived consequences to
  be shared safely between reasoners with different internal algorithms and
  different views of the search state.
- A formal import predicate specifying exactly when conditional knowledge may
  be consumed, together with an efficient implementation.
- A distributed protocol and implementation that avoids a single global trail,
  global decision level, or globally synchronized theory state.
- Hierarchical, utility-aware knowledge exchange that scales communication
  sublinearly relative to naive broadcast.
- A heterogeneous CPU/GPU solver in which accelerators perform algorithms
  suited to them and feed useful knowledge back into complete CPU reasoners.
- Experimental evidence on SMT-LIB benchmark families showing where the model
  scales, where it fails, and why.
- A sound proof/certificate aggregation story for distributed UNSAT results.

## 4.4 Novelty boundary (sharpened)

The novelty claim is not "parallel SAT with clause sharing" or "distributed
SMT." It rests on three axes that together distinguish ReasonMesh from prior
work:

| Axis | Prior art ceiling | ReasonMesh claim |
|---|---|---|
| **Knowledge generality** | HordeSat/Mallob share clauses only; even with utility scoring, the exchanged object is always a Boolean clause. | AKX defines a *typed* knowledge schema — clauses, theory lemmas, bounds, cubes, conflict cores, proof fragments — each with explicit assumption scoping. Theory lemmas and bounds are first-class bus citizens, not a private theory-solver internal. |
| **Assumption scoping** | Distributed SMT partitioning (Wilson et al. 2023, Zhao et al. 2024) assigns subproblems and collects full SAT/UNSAT answers; workers don't exchange intermediate logical consequences under shared assumption contexts. | AKX carries a formal validity predicate `F ∧ asmpts ⊨ concl` and a protocol by which an importer verifies its own context entails `asmpts` *before* applying the knowledge — enabling safe knowledge reuse across heterogeneous, independently searching workers. |
| **Accelerators as peers** | Prior GPU SAT work calls GPU code synchronously as a library subroutine within a CPU CDCL loop. | GPU workers in ReasonMesh are first-class AKX participants: they publish typed knowledge objects (model fragments, cubes, heuristic hints, circuit evaluations) that CPU workers consume asynchronously, and they are never a synchronization point in the CPU critical path. |

No prior published system combines all three. The paper's primary novelty
claim is the *formal AKX knowledge model with assumption scoping* and the
experimental evaluation of whether it delivers measurable benefits over
clause-only sharing.

---

# 5. Architectural Principles

| Principle | Meaning |
|---|---|
| Sound knowledge first | Every globally shareable item must have explicit semantics and provenance sufficient to establish the conditions under which it is valid. |
| No mandatory global trail | A local CDCL(T) worker may maintain a trail and decision levels, but other workers do not need to share or synchronize that trail. |
| Local autonomy | Workers are free to choose algorithms, heuristics, data layouts, and hardware-specific representations. |
| Asynchrony by default | Knowledge arrival is opportunistic. Correctness must not depend on workers receiving the newest information immediately. Liveness (eventual termination) is guaranteed separately — see §8.4. |
| Communication is a resource | Bytes transmitted, serialization, network latency, and import cost are accounted for as solver costs. |
| Hierarchy over broadcast | Knowledge should move through local, node, cluster, and global scopes according to estimated utility. |
| Accelerators are peers | GPU workers produce logical progress; they are not libraries called synchronously by a CPU solver. |
| Independent validation | SAT models and UNSAT certificates must be checkable outside the worker that produced them. |
| Reproducibility | Deterministic single-worker mode and capture/replay facilities are mandatory. |

---

# 6. System Architecture

```
┌──────────────────────────────────────────────────────────────────────┐
│                          ReasonMesh Process / Cluster                │
│                                                                      │
│  ┌────────────┐     ┌───────────────────────────────────────────┐   │
│  │  Front End │────▶│              Orchestrator                 │   │
│  │  SMT-LIB   │     │  (primary + hot-standby, §13.4)           │   │
│  │  Parser    │     │  admission · budgets · leases · cancel    │   │
│  └────────────┘     └───────────┬───────────────────────────────┘   │
│                                 │ WorkUnit dispatch                  │
│          ┌──────────────────────┼──────────────────────┐            │
│          ▼                      ▼                      ▼            │
│  ┌───────────────┐   ┌────────────────────┐  ┌──────────────────┐  │
│  │  CPU Reasoner │   │   GPU Reasoner     │  │ Theory Reasoner  │  │
│  │  CDCL(T)      │   │   BV circuits /    │  │ EUF / Arith /    │  │
│  │  local search │   │   candidate score  │  │ IDL / LRA        │  │
│  └──────┬────────┘   └────────┬───────────┘  └──────┬───────────┘  │
│         │  publish            │  publish             │  publish     │
│         ▼                     ▼                      ▼             │
│  ╔═══════════════════════════════════════════════════════════════╗  │
│  ║                     AKX Fabric (rm-akx + rm-bus)             ║  │
│  ║  typed knowledge · assumption scoping · dedup · utility      ║  │
│  ║  routing: worker → node → cluster → global                   ║  │
│  ║  back-pressure · eviction · version/schema negotiation       ║  │
│  ╚═══════════════════════════════════════════════════════════════╝  │
│         │  poll                │  poll                │  poll      │
│         ▼                      ▼                      ▼            │
│  ┌───────────────┐   ┌────────────────────┐  ┌──────────────────┐  │
│  │  Partitioner  │   │  Proof/Validation  │  │   Telemetry      │  │
│  │  cube split   │   │  model eval /      │  │   metrics /      │  │
│  │  work steal   │   │  cert reconstruct  │  │   replay log     │  │
│  └───────────────┘   └────────────────────┘  └──────────────────┘  │
└──────────────────────────────────────────────────────────────────────┘
```

*Figure 1. ReasonMesh high-level architecture. The AKX fabric carries
semantic knowledge; transport and hardware backends are below that abstraction.
The Orchestrator runs in primary/hot-standby pair (§13.4).*

Diagram source lives in `docs/figures/architecture.excalidraw`.

## 6.1 Major subsystems

| Subsystem | Responsibilities |
|---|---|
| Front End | SMT-LIB 2.7 parsing; type/sort checking; normalization; term interning; problem DAG; model symbol mapping. |
| Orchestrator | Worker admission; work budgets; decomposition; cancellation; termination detection; resource allocation; global experiment metadata. Runs as primary + hot-standby pair. |
| CPU Reasoners | CDCL/CDCL(T), local search, specialized theory-driven search, proof-producing complete workers. |
| GPU Reasoners | Batch Boolean/circuit evaluation, bit-vector kernels, candidate exploration, preprocessing/inprocessing kernels, GPU-friendly local search. |
| Theory Reasoners | EUF, difference logic, LRA/LIA, bit-vectors and later arrays; generate conflicts, propagations, lemmas, and bounds. |
| Partitioners | Generate cubes/subproblems; recursively split hard regions; estimate partition quality and duplication. Guarantee exhaustive coverage (§8.4). |
| AKX Fabric | Knowledge schema, local/global routing, deduplication, utility scoring, compression, back-pressure, persistence, and provenance. |
| Proof/Validation | Model validation, clause/theory proof fragments, distributed UNSAT certificate reconstruction, checker interfaces. |
| Telemetry | Metrics, traces, replay logs, per-worker provenance, and experiment manifests. |

---

# 7. AKX Knowledge Model

The central abstraction is a **knowledge object** — a conclusion together with
the assumptions and provenance under which it is valid. A globally shared
consequence must be usable without importing the sender's private control state.

```
Knowledge K = (kind, conclusion, assumptions, scope, provenance, utility, proof_ref)

Validity obligation:  F ∧ assumptions ⊨ conclusion
```

`F` here is the original problem formula, which is fixed and globally known.
`assumptions` is a set of literals forming a cube under which `conclusion` was
derived. Unconditional knowledge has `assumptions = ∅`.

## 7.1 Initial knowledge kinds

| Kind | Examples | Typical producers |
|---|---|---|
| Clause | ¬a ∨ ¬b ∨ c | CDCL workers, theory conflict explainers |
| TheoryLemma | x=y ∧ y=z ⇒ x=z | EUF/theory reasoners |
| Bound | x ≤ 14 | Arithmetic reasoners |
| Cube | a, ¬b, c | Partitioners, GPU search |
| ConflictCore | {x<3, x>8} | Theory reasoners |
| ModelFragment | partial assignment / candidate values | GPU/local-search workers |
| ProofFragment | resolution or theory certificate fragment | Proof-producing workers |
| HeuristicHint | activity / structural score | GPU analytics, portfolio learners |

**Trust levels:** `Clause`, `TheoryLemma`, `Bound`, `ConflictCore`, and
`ProofFragment` items produced by complete CPU reasoners are *trusted
consequences* — they may participate in UNSAT closure. `ModelFragment` and
`HeuristicHint` items and anything from GPU/local-search workers are *proposals*
— they require independent validation before influencing the UNSAT decision
(§13.1).

## 7.2 Rust-level interface

```rust
/// Fired by a Reasoner on each step; determines what the scheduler does next.
pub enum ReasonerEvent {
    /// Worker made progress; has knowledge to export.
    Progress,
    /// Worker found a satisfying assignment under its active assumptions.
    SatCandidate { model: Arc<PartialModel> },
    /// Worker proved UNSAT under its active assumptions (complete workers only).
    UnsatLocal { proof_ref: Option<ProofRef> },
    /// Worker exhausted its budget without conclusion; return and reschedule.
    BudgetExhausted,
    /// Worker needs a new work unit to continue.
    NeedWork,
    /// Worker has been cancelled and is shutting down cleanly.
    Cancelled,
    /// Unrecoverable internal error; worker must be restarted.
    InternalError(ReasonerError),
}

/// What a reasoner can produce/consume; used by the scheduler for routing.
pub struct Capabilities {
    pub can_produce: EnumSet<KnowledgeKind>,
    pub can_consume: EnumSet<KnowledgeKind>,
    /// Worker is complete: its UnsatLocal events may contribute to UNSAT closure.
    pub is_complete: bool,
    /// Worker produces checkable proof fragments.
    pub produces_proofs: bool,
    pub hardware: HardwareClass,
}

/// Snapshot sufficient for the orchestrator to restart a worker from scratch.
/// Does NOT need to be a full solver state copy — a work-unit + seed suffices
/// for deterministic workers; stateful workers may serialize more.
pub struct Checkpoint {
    pub worker_id: WorkerId,
    pub work_unit: WorkUnit,
    pub internal_state: Option<Vec<u8>>, // solver-defined opaque blob, may be None
    pub knowledge_watermark: KnowledgeId, // highest imported knowledge ID seen
    pub timestamp: Instant,
}

pub trait Reasoner {
    fn id(&self) -> ReasonerId;
    fn capabilities(&self) -> Capabilities;

    /// Import a batch of knowledge. Implementors MUST apply the import predicate
    /// (§7.3) before using any item with non-empty assumptions.
    fn import(&mut self, batch: KnowledgeBatch) -> Result<ImportStats, ReasonerError>;

    /// Run for at most `budget` units of work. Returns the event that ended the step.
    fn step(&mut self, budget: WorkBudget) -> Result<ReasonerEvent, ReasonerError>;

    /// Snapshot knowledge to export. Takes `&self` — does NOT mutate reasoner
    /// state. The scheduler tracks export watermarks externally.
    fn export(&self, policy: &ExportPolicy) -> Result<KnowledgeBatch, ReasonerError>;

    /// Return a lightweight checkpoint the orchestrator can persist.
    /// Returns None for stateless/seed-only workers.
    fn checkpoint(&self) -> Result<Option<Checkpoint>, ReasonerError>;
}
```

> **Why `export` takes `&self`:** Export is a read operation — it snapshots
> knowledge the reasoner has already derived. Taking `&mut self` would prevent
> concurrent export and step scheduling. The scheduler maintains a per-worker
> `ExportWatermark` (a monotonically increasing `KnowledgeId`) to track what
> has already been transmitted.

## 7.3 Formal import predicate and checking protocol

This is the central correctness invariant of AKX.

### Definition

A worker W with active assumption set `ctx_W` (the literals W is currently
assuming) may apply knowledge object K = `(kind, concl, asmpts, ...)` if and
only if:

```
IMPORT_OK(W, K)  ≡  ctx_W ⊇ asmpts
```

That is, every literal in K's assumption set must be entailed by W's current
context. For unconditional knowledge (`asmpts = ∅`), the predicate is always
true.

### Efficient checking

Naively, checking `ctx_W ⊇ asmpts` requires a set-membership test per literal
in `asmpts`. For typical clause knowledge with small assumption sets this is
O(|asmpts|) against W's assignment. For larger assumption sets:

1. **Literal ID sets:** Both `ctx_W` and `asmpts` are represented as sorted
   vectors of `Literal` (a `u32`). Subset check is a linear merge — O(|asmpts|).

2. **Bloom pre-filter:** Each worker maintains a Bloom filter over its current
   `ctx_W`. An `asmpts` batch is pre-screened: if the filter says "definitely
   not subset," skip the knowledge object before the linear merge.

3. **Assumption context hash:** Workers publish a context fingerprint
   (rolling Zobrist hash over `ctx_W`) with each export. The fabric can
   route knowledge only to workers whose fingerprint matches a pre-computed
   compatible-context set, reducing import attempts at the bus level.

4. **Theory lemma special case:** For `TheoryLemma` knowledge under a theory
   context (not just Boolean assumptions), the importer checks that:
   - The theory context identifiers in `asmpts` are a subset of its own
     active theory context (identified by a `TheoryContextId` token).
   - If the theory context is not a subset, the lemma is *buffered*, not
     discarded — it may become applicable when the worker's theory state
     changes.

### What to do with inapplicable knowledge

| Case | Action |
|---|---|
| `asmpts = ∅` (unconditional) | Always apply. |
| `ctx_W ⊇ asmpts` | Apply immediately. |
| `ctx_W ⊅ asmpts` but `ctx_W ∩ asmpts ≠ ∅` | Buffer; re-check on next context change. |
| `ctx_W ∩ asmpts = ∅` | Discard (no overlap; unlikely to become applicable soon). |

The buffer is bounded (configurable; default 1024 items per worker) and uses
LRU eviction by utility score.

### What import cannot do

Importing knowledge can never change a satisfiable problem instance into UNSAT.
Proof: K's validity obligation guarantees `F ∧ asmpts ⊨ concl`. If
`IMPORT_OK(W, K)` holds, then `F ∧ ctx_W ⊨ concl` (since `ctx_W ⊇ asmpts`).
W is searching for an assignment satisfying `F ∧ ctx_W`; importing `concl`
merely adds a derived consequence that is already entailed — it cannot
introduce a false contradiction.

---

# 8. Search and Parallelism Model

## 8.1 Three forms of parallelism

| Mode | Purpose | Scaling behavior |
|---|---|---|
| Portfolio | Different heuristics/algorithms solve the same problem. | Excellent at small/medium worker counts; diversity eventually saturates. |
| Decomposition | Workers solve assumption-scoped cubes/subproblems. | Enables recursive scale-out; must control duplication and partition quality. |
| Functional specialization | Workers perform different reasoning jobs. | Enables CPU/GPU/theory heterogeneity and asynchronous pipelines. |

## 8.2 Dynamic work units

```rust
pub struct WorkUnit {
    pub problem: ProblemId,
    pub assumptions: Arc<[Literal]>,
    pub theory_context: Option<ContextRef>,
    pub ancestry: CubePath,          // lineage for duplication detection
    pub priority: Priority,
    pub budget: WorkBudget,
    pub seed: u64,
    /// Shared cancellation token. Set to true when SAT is validated or the
    /// orchestrator cancels outstanding work. Workers MUST poll this in their
    /// step loop and return ReasonerEvent::Cancelled promptly.
    pub shutdown: Arc<AtomicBool>,
}
```

A worker may solve a work unit, return it with progress metadata, or split it
into children. Hard regions receive more resources without precomputing a
static partition tree.

## 8.3 Termination protocol

- **SAT:** A candidate model is returned and independently validated against
  the original assertions. On validation success, the orchestrator sets the
  global `shutdown` token and cancels all outstanding leases. Workers poll
  `WorkUnit::shutdown` in their step loops.

- **UNSAT:** Completeness depends on parallelism mode (see §8.4). The
  orchestrator uses a distributed termination detection protocol (Dijkstra–
  Scholten or token-ring) to confirm no in-flight messages or work units
  remain before declaring UNSAT.

- **UNKNOWN/TIMEOUT:** Budget expires without a validated SAT result or
  complete UNSAT closure.

- The termination protocol is an orchestrator-level concern; workers never
  directly broadcast a global UNSAT claim.

## 8.4 Completeness guarantees per mode (formal)

### Portfolio mode

**Claim:** If at least one worker is a complete CDCL(T) reasoner with
`is_complete = true` and it is not cancelled before it terminates, the
system is complete for any logic the worker supports.

**Argument:** A complete worker running to termination on the full problem
produces SAT or UNSAT independently of any imported knowledge (import can
only speed it up, never make it unsound — see §7.3 import safety proof).
Therefore, if all workers time out before termination, the system returns
UNKNOWN; it never returns a wrong answer.

### Decomposition mode

**Claim:** If the partitioner generates an exhaustive, non-overlapping cover
of the search space and every partition is eventually closed by a complete
worker, the system is complete.

**Exhaustiveness invariant (maintained by the partitioner):**

```
cover(root) = {literal_set_1, ..., literal_set_k}   where
  ∀ assignment α:  ∃ i. α ⊨ literal_set_i          (coverage)
  ∀ i ≠ j: ¬(literal_set_i ∧ literal_set_j) is satisfiable   (non-overlap is not required but duplication must be bounded)
```

The partitioner must maintain a *partition tree* in the orchestrator with:
- Each leaf node: open (assigned), closed-SAT, or closed-UNSAT.
- UNSAT closure requires *every* leaf to be closed-UNSAT.
- SAT closure requires *any* leaf to be closed-SAT (with a validated model).

**Cube splitting invariant:** When a work unit is split into children
`{c_1, ..., c_k}` with assumptions `{asmpts ∪ {l_1}, ..., asmpts ∪ {l_k}}`,
the literals `{l_1, ..., l_k}` must cover all satisfying extensions of
`asmpts` — i.e., `l_1 ∨ l_2 ∨ ... ∨ l_k` must be a tautology or derivable
from `F ∧ asmpts`. The partitioner generates a validity certificate for each
split; the orchestrator verifies it before recording the partition.

### Liveness under asynchrony

Workers do not need to receive the *latest* knowledge immediately (safety).
But for *liveness* (guaranteed eventual termination given an infinite budget):

- The AKX bus guarantees *eventual delivery*: any published knowledge item is
  delivered to every subscribed worker within a finite number of poll cycles
  (the bus does not silently drop items except via the defined eviction policy
  in §12.3, and eviction only applies under memory pressure with replacement
  by higher-utility items).
- A complete CPU worker that has received all relevant imported clauses up to
  a given point will eventually terminate on its assigned partition.
- Liveness is not blocked by GPU or local-search workers, since those workers
  are never on the critical UNSAT path.

---

# 9. CPU Solver Architecture

At least one production-quality complete CPU path is required. This is both
the correctness anchor and the fallback that preserves completeness while
experimental workers remain incomplete.

## 9.1 CDCL(T) worker requirements

- Two-watched-literal Boolean propagation, first-UIP conflict analysis,
  non-chronological backjumping, and restart policies.
- Modular branching heuristics (VSIDS/EVSIDS and later alternatives).
- Clause quality metrics including LBD, activity, size, age, origin, and
  observed import utility.
- Incremental assumption solving so that cube-based work units do not require
  full solver reconstruction.
- Import queues separated from propagation-critical structures; imported
  clauses are integrated in bounded batches.
- Theory interface with conflict explanation and theory propagation.
- Optional proof logging/certificate generation.

## 9.2 Distributed CPU hierarchy

```
worker threads → process/node exchange → cluster group → global exchange
```

High-value knowledge travels farther. Low-value knowledge remains local.

Initial routing policy uses clause length, LBD, reuse count, and age. Later
policies estimate marginal utility using telemetry. Routing thresholds are
learned empirically during milestone M2/M3 ablations.

---

# 10. GPU and Accelerator Architecture

The GPU design must begin from algorithms with regular data parallelism, high
arithmetic intensity, and bounded synchronization. The CDCL control loop does
not belong on the GPU.

## 10.1 Priority GPU workloads

| Priority | Kernel / workload | Research purpose |
|---|---|---|
| P0 | Bit-vector circuit evaluation over large batches | Flagship heterogeneous theory path; exploit packed operations and many candidate inputs. |
| P0 | Mass candidate/cube scoring | Find promising assignments/branch restrictions and feed cubes/hints to CPU reasoners. |
| P1 | Bulk clause state evaluation / preprocessing | Evaluate millions of clause/literal relationships without CPU cache pressure. |
| P1 | GPU local search | Explore many stochastic trajectories independently; export models/cubes/hints. |
| P2 | Selected inprocessing kernels | Subsumption-like or structural passes where transfer cost is amortized. |
| P2 | Theory-specific matrix/vector kernels | Only where arithmetic structure makes end-to-end acceleration plausible. |

## 10.2 Accelerator interface

```rust
pub trait AcceleratorBackend {
    fn upload_problem(&mut self, problem: &AcceleratorIR) -> Result<DeviceProblem, AccelError>;
    fn evaluate_candidates(
        &mut self,
        p: &DeviceProblem,
        c: &CandidateBatch,
    ) -> Result<CandidateScores, AccelError>;
    fn evaluate_circuit(
        &mut self,
        p: &DeviceCircuit,
        inps: &InputBatch,
    ) -> Result<OutputBatch, AccelError>;
    fn synchronize(&mut self) -> Result<AcceleratorStats, AccelError>;
}
```

> **Acceptance criterion for GPU work:** A GPU kernel is not considered
> successful because its kernel time beats a CPU microbenchmark. It must
> improve *end-to-end solve time* or materially improve solved-instance
> coverage under a fixed wall-clock/resource budget.

## 10.3 GPU memory and transfer budget

For each P0 workload the implementation must profile and document:

- Peak GPU memory usage vs. problem size (circuit size, candidate batch size).
- PCIe/NVLink transfer time as a fraction of kernel time.
- The problem size at which GPU memory is exhausted and spilling strategy
  (tiled evaluation, host-pinned streaming, or problem size limit).

GPU work is gated by G3 (§18): if end-to-end wins on a defined BV benchmark
subset cannot be demonstrated, GPU reasoners are kept experimental and do not
appear as headline claims in the paper.

---

# 11. Theory Roadmap

Theory support is ordered to serve the research question, not to maximize
SMT-LIB feature count.

| Stage | Logic / capability | Reason |
|---|---|---|
| T0 | Propositional SAT | Validates distributed AKX, portfolio, partitioning, and proof/certificate plumbing. |
| T1 | QF_BV | Best early GPU/accelerator target; rich industrial relevance; can combine circuits and bit-blasting. |
| T2 | QF_UF / EUF | Clean theory-lemma and explanation model; validates generalized knowledge exchange. |
| T3 | Difference logic (IDL/RDL) | Graph-based arithmetic milestone with clearer explanations and parallel experiments. |
| T4 | QF_LRA / QF_LIA | Serious arithmetic; enables comparisons with distributed SMT partitioning literature. |
| T5 | Arrays / theory combinations | Tests Nelson-Oppen-style combinations. See §11.1 for the asynchrony tension. |
| Later | Quantifiers, strings, FP, nonlinear | Only after the scalable architecture is demonstrated or falsified. |

## 11.1 Nelson-Oppen and asynchrony — the tension and resolution

Nelson-Oppen theory combination requires theory solvers T₁ and T₂ to exchange
equalities in a synchronized round-robin until a fixed point is reached. This
is in direct tension with AKX's "asynchrony by default" principle.

**Resolution strategy for T5:**

1. **Within-worker synchronous NO:** Each CPU CDCL(T) worker runs its own
   local Nelson-Oppen loop synchronously. This is not a global barrier — it
   is local to one worker's theory stack. This is the same approach taken by
   Z3 and cvc5: the Nelson-Oppen loop is inside one solver instance.

2. **Between-worker asynchronous exchange:** When a worker's NO loop produces
   a new shared equality (e.g., `x = y` derived by both EUF and arithmetic),
   that equality is published to AKX as a `TheoryLemma` with the worker's
   current assumption context. Other workers may import it and use it to
   accelerate their own NO loops — but they are never *required* to, and
   they never wait for it.

3. **Completeness is not compromised:** Each complete CPU worker running its
   own full NO loop to convergence is complete for combined theories. The
   asynchronous exchange of NO-derived equalities between workers is a
   performance optimization, not a correctness dependency.

**Consequence:** AKX does not implement distributed Nelson-Oppen. It implements
independent per-worker Nelson-Oppen with opportunistic theory-lemma sharing.
This must be stated clearly in the paper to avoid misleading claims.

---

# 12. AKX Transport and Communication

## 12.1 Transport independence with back-pressure

```rust
pub trait KnowledgeBus {
    /// Publish a batch to the given scope.
    /// Returns a handle for tracking delivery and a Result for back-pressure.
    /// Err(BusError::BufferFull) signals the producer to slow down.
    fn publish(
        &self,
        scope: Scope,
        batch: EncodedKnowledgeBatch,
    ) -> Result<PublishHandle, BusError>;

    /// Poll for available knowledge. Non-blocking; returns empty batch if none.
    fn poll(&self, budget: PollBudget) -> Result<EncodedKnowledgeBatch, BusError>;

    fn metrics(&self) -> BusMetrics;
}

pub enum BusError {
    BufferFull,      // producer must back off
    Disconnected,    // transport layer failure
    SchemaRejected,  // version mismatch; message dropped
    Internal(String),
}
```

Initial implementations: in-process bounded MPSC queues and TCP/QUIC network
transport. RDMA/MPI can be explored later; solver semantics must not depend
on either.

## 12.2 Communication policies

- Batch knowledge to amortize serialization and transport overhead.
- Deduplicate by canonical hash before expensive import work (see §12.4 for
  canonical hash definition).
- Apply hierarchical scope: worker → node → cluster → global.
- Rate-limit export based on bytes/sec and import CPU cost, not merely number
  of clauses.
- Maintain per-origin and per-kind utility measurements.
- Allow stale knowledge; do not insert global barriers for freshness.
- Carry version/schema identifiers to enable protocol evolution.
- When `BusError::BufferFull` is returned to a producer, the producer backs
  off for one step before retrying. Producers with lower utility scores back
  off longer (exponential with utility-weighted jitter).

## 12.3 Buffer limits and eviction policy

Each scope level maintains a bounded ring buffer:

| Scope | Default buffer limit | Eviction policy |
|---|---|---|
| Worker-local | 64 MB | LRU by last-access time |
| Node | 256 MB | Lowest utility score first |
| Cluster | 1 GB | Lowest utility score; then oldest |
| Global | Configurable | Lowest utility score; then oldest |

When a buffer is full, the incoming item is compared against the lowest-utility
item in the buffer:
- If the incoming item's utility > lowest item's utility: evict lowest, insert
  incoming.
- Otherwise: return `BusError::BufferFull` to the producer.

Utility score is a weighted combination of: knowledge kind weight, LBD (for
clauses), reuse count, source reliability score, and age decay. Weights are
initially hand-tuned and refined using telemetry data.

## 12.4 Canonical hash for assumption-scoped knowledge

Deduplication must be *sound*: two knowledge objects are duplicates only if
they are logically identical under the same assumptions.

```
canonical_hash(K) = hash(K.kind_tag ‖ canonical_form(K.conclusion) ‖ sorted(K.assumptions))
```

- `canonical_form` normalizes the conclusion (e.g., sorts clause literals by
  variable ID, normalizes polarity).
- `sorted(K.assumptions)` sorts assumption literals by their `u32` ID.
- Two objects with identical `canonical_hash` are considered duplicates.

**Consequence:** The same clause derived under `asmpts = {}` and under
`asmpts = {a}` have *different* canonical hashes and are not deduplicated —
the unconditional one is strictly stronger and should replace the conditional
one if both are present. The bus tracks this: if an unconditional version of
a conclusion is present, conditional versions of the same conclusion are
evicted as redundant.

---

# 13. Correctness, Proofs, and Fault Tolerance

## 13.1 Soundness invariant and trust levels

No worker is trusted merely because it is part of the cluster. Knowledge
objects are classified by trust level at publish time:

| Trust level | Who can assert it | May contribute to UNSAT closure |
|---|---|---|
| `Trusted` | Complete CPU CDCL(T) workers with `is_complete = true` | Yes |
| `Proposal` | GPU workers, local-search workers, incomplete reasoners | No — must pass validation |
| `Hint` | Heuristic scorers, portfolio learners | No — used only for branching/routing |

GPU workers and local-search workers may propose `ModelFragment` and `Cube`
knowledge as `Proposal` trust level. A `Proposal` model fragment triggers
model validation (§13.2) before SAT is declared. A `Proposal` cube is used
for branching hints but never for UNSAT closure.

Experimental workers that gain a correctness track record over a run may be
*promoted* to `Trusted` by the orchestrator, but this is a future extension
and is not part of the initial design.

## 13.2 Result validation

| Result | Required validation |
|---|---|
| SAT | Evaluate the model against the original normalized assertions using an independent model evaluator written in a separate crate from the solver. |
| UNSAT (SAT layer) | Proof/checkable certificate when supported; otherwise cross-check in regression testing. Only `Trusted` workers may close partitions for UNSAT. |
| UNSAT (SMT) | Aggregate Boolean and theory proof fragments or use a trusted proof-producing worker to close the result. |
| GPU candidate | Never accepted directly as UNSAT. SAT candidate must pass independent model validation before SAT is declared. |

## 13.3 Failure model

- Worker process crash loses performance, not soundness.
- Duplicate messages are harmless (deduplication by canonical hash).
- Reordered knowledge is harmless (import predicate is stateless per object).
- Delayed knowledge is harmless for correctness; see §8.4 for liveness bounds.
- Lost heuristic hints are harmless; loss of partition ownership triggers
  lease expiry and reassignment by the orchestrator.
- Malformed or incompatible network messages are rejected at the schema
  validation layer before entering the solver import path.

## 13.4 Orchestrator high availability

The orchestrator is a potential single point of failure. For cluster
experiments the orchestrator runs as a **primary + hot-standby pair**:

- The primary orchestrator persists all partition tree state, lease
  assignments, and work-unit lineage to a replicated write-ahead log (WAL)
  after each mutation.
- The standby replays the WAL and maintains an in-memory shadow of the
  partition tree.
- On primary failure, the standby promotes itself within one heartbeat
  interval (configurable; default 5 seconds).
- Workers detect orchestrator failure via heartbeat timeout and reconnect to
  the standby.
- In-flight work units during failover continue executing; their lease timers
  are reset on reconnect.

For single-machine and small-cluster experiments the orchestrator may run
without a standby, accepting that orchestrator failure terminates the
experiment.

---

# 14. Proposed Rust Workspace

```
reasonmesh/
├── crates/
│   ├── rm-syntax/          # SMT-LIB parser, sorts, AST
│   ├── rm-ir/              # interned term DAG, Boolean/circuit IR
│   ├── rm-sat/             # production CDCL core
│   ├── rm-smt/             # Boolean abstraction and CDCL(T) integration
│   ├── rm-theory-euf/
│   ├── rm-theory-bv/
│   ├── rm-theory-arith/
│   ├── rm-akx/             # knowledge model, import predicate, policies
│   ├── rm-bus/             # in-proc + network transports
│   ├── rm-scheduler/       # work units, leases, decomposition, partition tree
│   ├── rm-worker/          # worker lifecycle/runtime
│   ├── rm-gpu/             # accelerator-neutral interface
│   ├── rm-gpu-cuda/        # optional CUDA backend
│   ├── rm-proof/           # certificates and reconstruction
│   ├── rm-telemetry/
│   ├── rm-bench/
│   └── reasonmesh-cli/
├── tests/
│   ├── unit/               # per-crate unit tests (also live alongside src/)
│   ├── integration/        # cross-crate: AKX import/export, CDCL+theory
│   ├── differential/       # compare against Z3/cvc5 oracles
│   └── distributed/        # fault injection, multi-node
├── fuzz/
│   ├── smt_parser/
│   ├── akx_decoder/
│   └── proof_checker/
├── benchmarks/
├── experiments/            # pinned run configs and data for paper
└── docs/
    ├── architecture_spec.md   # this file
    └── figures/
```

## 14.1 Dependency rules

- `rm-sat` and theory crates must not depend on network or GPU crates.
- `rm-akx` defines semantic messages; `rm-bus` only transports encoded messages.
- `rm-worker` adapts a reasoner to runtime/scheduling; algorithm crates remain
  runnable in-process for deterministic tests.
- GPU backends depend on accelerator-neutral IR, never on mutable internal
  SAT clause structures.
- Telemetry is append-only/observational and must not be required for
  correctness.
- `rm-proof` model evaluator must not share code with solver internals — the
  point is independent verification.

---

# 15. Verification and Test Specification

## 15.1 Test pyramid

| Layer | Examples | Gate |
|---|---|---|
| Unit | Literal encoding, watched lists, union-find rollback, serialization, proof steps | Every commit |
| Property | CNF/model invariants, Boolean identities, theory algebraic properties, import predicate invariants | Every commit / CI |
| Exhaustive oracle | Small SAT, small bit-vectors, tiny EUF domains where feasible | CI + nightly |
| Differential | Compare with Z3/cvc5 or SAT competition solvers | Nightly / release |
| Fuzz | SMT-LIB parser, IR, AKX protocol decoder, proof checker | Continuous corpus |
| Distributed fault | Kill/restart workers, reorder/duplicate/delay messages | Nightly / cluster CI |
| Scale | 1…N CPU workers, 0…M GPUs, multi-node runs | Milestone / paper experiments |
| Regression | Every discovered disagreement becomes a permanent testcase | Always |

## 15.2 Core correctness properties

- Single-worker result equals brute-force oracle on generated small Boolean
  formulas.
- QF_BV operations match Rust modular arithmetic exhaustively at small bit
  widths.
- Imported knowledge cannot change a satisfiable problem into UNSAT (proven
  in §7.3; tested by property tests that inject random knowledge into
  satisfiable instances and verify result is still SAT or UNKNOWN).
- 1-worker, N-worker, and GPU-enabled configurations agree on SAT/UNSAT for
  regression sets.
- Every SAT model validates independently.
- Worker loss, duplicate messages, and message reorder do not change logical
  result.
- Partition coverage is complete: sibling cubes cover the parent search region
  and do not silently omit cases (partitioner emits a coverage certificate
  per split; tested in property tests).
- Any proof/certificate accepted by the checker derives the claimed result.
- Import predicate is enforced: fuzzer injects knowledge objects with
  incorrect assumptions and verifies the solver rejects or buffers them
  without using them unsoundly.

## 15.3 Deterministic and replay modes

```
reasonmesh solve --workers 1 --gpu off --seed 1 --deterministic problem.smt2
reasonmesh replay experiment/run-0042.rmtrace
```

Replay logs capture: random seeds, work-unit lineage, imported/exported
knowledge IDs, worker configuration, solver version, hardware metadata, and
timing boundaries. Exact timing need not replay, but logical event ordering
within a worker must.

---

# 16. Benchmark and Performance Specification

## 16.1 Benchmark families

**Primary (external, unmodified — these drive paper claims):**

- SAT Competition application benchmarks for validating massive Boolean scaling
  and comparison with distributed SAT literature.
- SMT-LIB benchmark families beginning with QF_BV, QF_UF, QF_IDL/QF_RDL,
  QF_LRA, and QF_LIA.
- Real verification-derived bit-vector benchmarks where circuit structure is
  preserved before bit-blasting.

**Secondary (synthetic — used for ablations only, not headline claims):**

- Controlled benchmarks designed to vary clause sharing utility, decomposition
  quality, communication pressure, and GPU batchability.
- Synthetic benchmarks are designed after examining the external results, not
  before, to avoid inadvertent tuning.

## 16.2 Mandatory metrics

| Category | Metrics |
|---|---|
| Outcome | SAT/UNSAT/UNKNOWN, solved count, PAR-2/PAR-10 where appropriate. |
| Time | Wall time, CPU time, time-to-first-useful-knowledge, startup and scheduling time. |
| Search | Decisions, propagations, conflicts, restarts, explored cubes, duplicate work estimate. |
| Knowledge | Generated/imported/used/discarded by kind, LBD/size distributions, reuse, propagation impact. |
| Network | Bytes sent/received, batch size, serialization time, latency, dropped/deduplicated messages. |
| GPU | Upload/download time, kernel time, occupancy/utilization, batch size, CPU stalls, end-to-end delta. |
| Scaling | Speedup, parallel efficiency, cost-normalized speedup, strong/weak scaling. |
| Reliability | Worker failures, reassignment time, lost work, recovery overhead. |

## 16.3 Experiment baselines

1. ReasonMesh single-worker deterministic configuration.
2. ReasonMesh multi-worker portfolio *without* knowledge sharing.
3. ReasonMesh with clause-only sharing (approximates HordeSat/Mallob baseline).
4. ReasonMesh with generalized AKX sharing (full typed knowledge).
5. Portfolio vs. decomposition vs. hybrid.
6. CPU-only vs. CPU+GPU under equal wall-clock and resource-cost views.
7. Current Z3/cvc5 releases at experiment time.
8. Relevant distributed approaches where reproducible artifacts are available
   (Mallob, Wilson et al. 2023 artifact if available).

Baselines 1–4 form the key ablation ladder for the paper: the marginal value
of each AKX feature is isolated.

---

# 17. Development Milestones

| Milestone | Deliverables | Exit criterion |
|---|---|---|
| M0 — Research harness | Repository, CI, benchmark manifest, telemetry schema, deterministic CLI. | A run is reproducible and produces machine-readable metrics. |
| M1 — Production SAT core | CDCL, watched literals, 1-UIP, restarts, model output, proof hook. | Zero disagreements on exhaustive small tests; competitive correctness on standard SAT corpus. |
| M2 — AKX local mesh | Reasoner API (full types), knowledge schema, in-process bus with back-pressure, N CPU workers, import predicate enforced. | Clause sharing works without global trail; deterministic 1-worker remains intact; import predicate fuzz tests pass. |
| M3 — Distributed CPU | Network bus, hierarchy, leases, scheduler, dynamic cubes, partition tree with coverage certificates, orchestrator HA. | Scales across multiple nodes; survives worker loss; measurable speedup on hard SAT set. |
| M4 — QF_BV | SMT front end, BV IR, bit-blasting and/or circuit path. | Differentially correct against reference SMT solvers. |
| M5 — GPU reasoners | Candidate/circuit kernels, GPU local-search or scoring reasoner, GPU memory/transfer profiling. | End-to-end wins on a defined BV benchmark subset, not just kernel wins. |
| M6 — Generalized SMT AKX | EUF + arithmetic theory knowledge and assumption-scoped exchange; per-worker NO loop with async theory-lemma sharing. | Cross-theory knowledge model validated; no unsound imports in stress tests. |
| M7 — Proof/certificate path | Proof fragments, aggregation/checker integration. | Distributed UNSAT result can be independently checked for selected logics. |
| M8 — Paper experiment freeze | Pinned commit, hardware manifests, scripts, benchmark lists, raw data. | All paper figures/tables reproducible from artifact. |

---

# 18. Research Decision Gates

The following gates prevent the project from spending years adding theories
before testing its central hypothesis.

| Gate | Question | Decision |
|---|---|---|
| **G0 after M1** (pivot risk) | Does the CDCL core design cleanly support assumption-scoped importing without structural changes to the trail or clause database? | If no, redesign the import interface before building the distributed layer. This gate specifically checks that the SAT-first validation will transfer to the SMT layer. |
| **G1 after M2** | Does asynchronous clause exchange improve multi-core SAT over isolated portfolios on hard instances? | If no, fix knowledge utility/routing before adding distributed complexity. |
| **G2 after M3** | Does the design scale beyond one machine without communication dominating? | If no, redesign hierarchy/batching/decomposition. |
| **G3 after M5** | Can GPU reasoners improve end-to-end solving for a meaningful BV subset? | If no, keep GPU experimental; do not contaminate core architecture or make GPU claims in the paper. |
| **G4 after M6** | Does generalized theory knowledge (lemmas, bounds) add measurable value beyond clauses/cubes alone? | If no, narrow paper claims to demonstrated knowledge kinds only. |
| **G5 before paper** | Are results reproducible and statistically defensible? | No submission until the experiment artifact regenerates all headline claims. |

---

# 19. Sharper Research Paper Proposal

## 19.1 The sharpening argument

The v0.1 spec proposed a paper that tries to prove the value of AKX across
all seven research questions simultaneously (RQ1–RQ7). This is too broad for
a single journal paper and risks diluted contributions. Below is a sharper,
more focused paper with a tighter thesis and stronger falsifiability.

## 19.2 Proposed paper

### Title

**"Assumption-Scoped Knowledge Exchange in Parallel SMT Solving: When Typed
Inter-Worker Communication Outperforms Clause Sharing"**

### Thesis (one sentence)

Typed, assumption-scoped knowledge objects — carrying theory lemmas, bounds,
and conflict cores alongside learned clauses — provide measurably greater
parallel scaling benefit than clause-only sharing on structurally
theory-heavy SMT instances, and the marginal benefit of each knowledge type
is quantifiably isolable via ablation.

### Why this is sharper than v0.1

The v0.1 thesis asked "can AKX work?" — a yes/no question about a large
architectural bet. This thesis asks "what is the marginal value of typed
knowledge over clause-only sharing?" — a quantitative question with a
falsifiable, independently interesting answer. A negative result ("theory
lemmas don't help at N workers") is as publishable as a positive one.

The GPU/accelerator story is deliberately separated out (see §19.5) so that
the core architectural claim is not contingent on GPU engineering succeeding.

### Focused research questions (4, not 7)

| RQ | Question | Measured by |
|---|---|---|
| RQ1 | What is the marginal parallel speedup from each knowledge kind (clauses only → + theory lemmas → + bounds → + cubes) relative to a clause-only baseline? | Ablation ladder on SMT-LIB QF_BV, QF_UF, QF_IDL benchmark families; PAR-2 and solved count. |
| RQ2 | At what worker count and communication load does the marginal benefit of each knowledge kind saturate or reverse? | Strong-scaling curves from 1 to 128 workers; communication cost fraction. |
| RQ3 | Does assumption-scoped knowledge exchange (AKX) preserve soundness under adversarial conditions (stale knowledge, reordered messages, worker failure)? | Fault injection test suite; zero soundness violations in 10^6 random-knowledge injection trials. |
| RQ4 | How does hierarchical routing (worker → node → global) affect the benefit/cost ratio of each knowledge kind? | Routing ablation: flat broadcast vs. two-level vs. full hierarchy on multi-node runs. |

### What is explicitly out of scope for this paper

- Distributed proof/certificate reconstruction (left for a follow-up).
- GPU reasoners as first-class contributors (§19.5 below).
- Quantifiers, strings, floating point, nonlinear theories.
- Completeness at scale beyond what the formal argument in §8.4 establishes.

### Expected structure

1. Introduction: limits of clause-only sharing in SMT; the knowledge
   generalization hypothesis.
2. Background: CDCL(T), HordeSat/Mallob (clause sharing), Cube-and-Conquer,
   Wilson et al. / Zhao et al. (distributed SMT partitioning).
3. AKX formal model: knowledge objects, validity obligation, assumption
   scoping, import predicate (§7.3 of this spec).
4. ReasonMesh architecture: reasoner API, bus, routing, partition tree.
5. Knowledge routing and utility policies.
6. Soundness argument and import predicate correctness proof.
7. Experimental methodology: benchmark families, ablation ladder, baselines.
8. Results: RQ1–RQ4 with ablation tables and scaling plots.
9. Threats to validity: benchmark selection bias, synthetic workload
   representativeness, hardware-specific results.
10. Related work.
11. Conclusions: which knowledge kinds help, when, and at what communication
    cost.

### Target journals (ordered by fit for this tighter contribution)

| Venue | Fit | Notes |
|---|---|---|
| **Journal of Automated Reasoning (JAR)** | Primary | The formal knowledge model + rigorous experimental ablation is exactly JAR's target contribution profile. |
| **STTT** | Secondary | Strong if the artifact and engineering quality are emphasized. |
| **TOCL** | Tertiary | If the formal model and import predicate proof expand substantially. |

### Minimum evidence before submission (tighter than v0.1)

- Pinned, publicly reproducible solver artifact and experiment scripts
  (SMT-LIB and Mallob/HordeSat comparison reproducible from artifact).
- Formal soundness argument for the import predicate with a machine-checked
  sketch (Lean or Coq optional but strongly preferred).
- Ablation ladder (baselines 1–4 from §16.3) on ≥ 3 SMT-LIB benchmark
  families.
- Strong-scaling data to ≥ 32 workers on a shared-memory machine; multi-node
  data to ≥ 2 nodes.
- Fault injection results demonstrating zero soundness violations.
- Explicit negative results: which knowledge kinds did not help, on which
  benchmark families, and at what worker counts.
- Independent model validation for all SAT results.
- Raw data for all tables and plots.

## 19.3 GPU companion paper (separate, later)

The GPU work is architecturally interesting but requires its own evaluation
story. A companion paper — *"GPU Reasoners as AKX Peers: Asynchronous
Bit-Vector Acceleration in ReasonMesh"* — can be submitted after G3 is
passed (§18), with its own ablation (CPU-only vs. CPU+GPU under equal
resource budgets) and its own analysis of transfer costs. This keeps the
core paper's thesis clean.

---

# 20. Major Technical Risks

| Risk | Why it matters | Mitigation |
|---|---|---|
| Communication overwhelms search | Mass sharing can make more workers slower. | Hierarchical scopes, utility filters, batching, import budgets, back-pressure, telemetry-driven policies. |
| Search duplication | Many workers may explore equivalent regions. | Dynamic partitioning, ancestry tracking, cube diversity metrics, work stealing. |
| Theory knowledge hard to generalize | Different theories expose incompatible internal state. | Keep shared knowledge semantic and assumption-scoped; do not share raw solver internals. |
| GPU transfer/synchronization costs dominate | Fast kernels may still slow whole solver. | Persistent device IR, large batches, asynchronous pipelines, strict G3 gate. |
| Proof reconstruction explodes | Distributed derivations create provenance volume. | Proof IDs, selective logging, hierarchical proof composition, optional trusted complete closer. Proof reconstruction deferred to companion work. |
| Rust performance pitfalls | Allocation/Arc/serialization overhead can dominate. | Arena allocation, compact literal IDs, zero-copy batches, profiling from M1 onward. |
| Feature creep | Adding theories can hide failure of research thesis. | Enforce research decision gates and milestone exit criteria strictly. |
| SAT-to-SMT pivot risk | AKX design validates at SAT layer but may require structural changes at SMT layer. | G0 gate (§18) checks this immediately after M1 before distributed investment. |
| Nelson-Oppen / asynchrony mismatch | Theory combination requires synchronization that conflicts with AKX principles. | Resolution defined in §11.1: per-worker synchronous NO with async theory-lemma sharing. Must be stated explicitly in paper. |
| Synthetic benchmark overfitting | Paper claims rest on benchmarks designed by the same team. | External SMT-LIB/SAT Competition benchmarks are primary; synthetics are ablation-only (§16.1). |

---

# 21. Recommended Implementation Order

1. Freeze knowledge IDs, assumptions, experiment manifest, and deterministic
   execution conventions. Define all types in §7.2 completely before writing
   solver code.
2. Build the production CDCL core with independent model validation and proof
   hooks. Validate G0 (import interface compatibility) immediately.
3. Build in-process AKX with full import predicate enforcement and back-pressure.
   Run 2–64 diversified CPU workers with controlled clause exchange.
4. Add utility telemetry and hierarchical local routing; perform ablation
   studies (baselines 1–3) immediately after M2.
5. Add distributed work units, leases, dynamic cube splitting, partition tree
   with coverage certificates, and network transport. Add orchestrator HA.
6. Demonstrate multi-node scaling on SAT before moving to flagship SMT.
7. Implement QF_BV with a circuit-oriented intermediate representation.
8. Add the first GPU reasoner; require end-to-end wins (G3) before paper GPU
   claims.
9. Add EUF and then arithmetic, extending the knowledge schema only when a
   theory requires it. Implement per-worker NO with async theory-lemma sharing.
10. Freeze paper experiment release; regenerate all tables from artifact.

---

# 22. External Interfaces

## 22.1 CLI

```
reasonmesh solve problem.smt2
reasonmesh solve --workers 64 problem.smt2
reasonmesh solve --cluster cluster.toml problem.smt2
reasonmesh solve --gpu auto --workers 128 problem.smt2
reasonmesh solve --deterministic --workers 1 --seed 1 problem.smt2
reasonmesh benchmark manifest.toml
reasonmesh replay run.rmtrace
reasonmesh check-proof result.rmproof
```

## 22.2 Configuration principle

A run must be describable by a versioned configuration file so that command
lines do not become the experiment specification. Hardware, worker portfolio,
knowledge policy, budgets, and theory settings are captured in the run
manifest. Every paper experiment has a corresponding pinned manifest in
`experiments/`.

---

# 23. Related Work

| Ref | Citation | Relevance |
|---|---|---|
| [1] | T. Balyo, P. Sanders, C. Sinz. "HordeSat: A Massively Parallel Portfolio SAT Solver." SAT 2015. arXiv:1505.03340. | Demonstrates decentralized, hierarchical, massively parallel portfolio SAT with clause exchange. ReasonMesh's clause-only baseline approximates this. |
| [2] | D. Schreiber, P. Sanders. "Scalable SAT Solving in the Cloud." 2022. arXiv:2205.06590. | Mallob introduces malleable distributed SAT solving and communication-efficient clause sharing. Primary comparison baseline. |
| [3] | A. Wilson et al. "Partitioning Strategies for Distributed SMT Solving." FMCAD 2023 / arXiv:2306.05854. | Studies divide-and-conquer partitioning for parallel SMT. Closest precursor to ReasonMesh's decomposition mode. |
| [4] | M. Zhao et al. "Distributed SMT Solving Based on Dynamic Variable-Level Partitioning." 2024. | Dynamic variable-level partitioning across cvc5, OpenSMT2, and Z3. |
| [5] | C. Barrett, P. Fontaine, C. Tinelli. "The SMT-LIB Standard: Version 2.7." SMT-LIB initiative. | Target language standard for the public interchange layer. |
| [6] | H. Barbosa et al. "cvc5: A Versatile and Industrial-Strength SMT Solver." TACAS 2022. | Reference implementation and system baseline for modern SMT capabilities. |
| [7] | M. Heule, M. Kullmann, V. Manthey, A. Biere. "Cube and Conquer: Guiding CDCL SAT Solvers by Lookaheads." HVC 2011. | Precursor to dynamic decomposition with cube-based work units. ReasonMesh's dynamic partitioning is an SMT generalization of this approach; must be explicitly cited and distinguished. |
| [8] | Journal of Automated Reasoning. Aims and Scope. Springer Nature. | Primary target journal. |
| [9] | International Journal on Software Tools for Technology Transfer. Aims and Scope. Springer Nature. | Secondary target journal. |
