# Paper Structure: ReasonMesh

**Target venue:** Journal of Automated Reasoning (JAR)
**Working title:** *ReasonMesh: Parallel DPLL(T) via Assumption-Scoped Knowledge Exchange*

---

## Abstract

SMT solvers underpin formal verification, synthesis, and automated reasoning, yet they remain largely sequential. Parallelizing DPLL(T) is non-trivial: naively sharing clauses across workers with different assumption sets corrupts the global proof state and can unsoundly prune satisfying branches. We present **ReasonMesh**, a parallel SMT solver built around the *Assumption-scoped Knowledge Exchange* (AKX) protocol. AKX formalizes four typed knowledge channels — theory lemmas, backbone inferences, solution hints, and conflict summaries — each carrying the assumption context under which it was derived. A worker may integrate an incoming message only when its current context subsumes the message's scope, preserving soundness without global locking. We implement AKX as a publish–subscribe worker pool layered on top of a standard CDCL(T) core with Simplex-based linear arithmetic and congruence closure for uninterpreted functions. On the SMT-LIB benchmark suite (QF_LIA, QF_UFLIA, QF_IDL, QF_UF), ReasonMesh achieves competitive results with Z3 across satisfiable and unsatisfiable instances. An ablation study isolates the contribution of each knowledge type, showing that backbone inferences account for the largest speedup on UNSAT instances while solution hints dominate on SAT instances. ReasonMesh is open source.

---

## 1. Introduction

**Hook:** SMT is the engine of modern verification. Sequential bottleneck is a first-class problem.

**Gap:** Existing parallel SMT approaches (portfolio solvers, cube-and-conquer) either ignore theory interaction or require a central coordinator that becomes a bottleneck. No principled framework for *typed, scoped* knowledge exchange exists.

**Contribution preview:** AKX fills this gap. We formalize the protocol, prove soundness, implement it, and measure it.

**Roadmap paragraph.**

---

## 2. Background

### 2.1 DPLL(T)

Standard CDCL(T) loop. Theory interfaces: `assert`, `check`, `explain`, `backtrack`. Simplex and congruence closure as running examples.

### 2.2 Challenges in Parallel SMT

- Clause sharing vs. assumption scope mismatch.
- Theory state is not trivially shareable (Simplex tableau, e-classes).
- Prior work: ManySAT (clause sharing), CVC5 parallel mode, cube-and-conquer for pure SAT.

---

## 3. AKX: Assumption-Scoped Knowledge Exchange

*This is Contribution 1: the formal framework.*

### 3.1 Assumption Contexts

Define assumption context Γ as the set of decision literals at the point of derivation. A fact F derived under Γ is valid in any context Γ' ⊇ Γ.

### 3.2 Knowledge Types

Four message types with formal soundness conditions:

| Type | Carrier | Scope rule |
|------|---------|------------|
| Theory lemma | Clause C derived by theory T | Γ = ∅ (globally valid) |
| Backbone inference | Unit literal l inferred at root | Γ = ∅ |
| Solution hint | Partial assignment σ | Γ ⊇ assumptions(σ) |
| Conflict summary | Learned clause C with tag | Γ ⊆ current context |

### 3.3 Soundness Theorem

**Theorem (AKX soundness):** If each worker integrates only messages whose scope is subsumed by its current context, the parallel search is sound (SAT iff any worker returns SAT; UNSAT iff all workers return UNSAT or a globally valid refutation is found).

*Proof sketch:* By induction on derivation steps. Each integration step is equivalent to a local unit propagation or clause addition under a compatible context.

### 3.4 Completeness

Completeness follows from the sequential completeness of CDCL(T): in the worst case, all workers behave sequentially with no message integration. AKX adds information; it never removes it.

---

## 4. Implementation

*This is Contribution 2: the protocol and system.*

### 4.1 Worker Pool Architecture

Diagram: N workers, shared message bus, per-worker CDCL(T) state.

### 4.2 Message Bus

Pub–subscribe ring buffer. Workers publish typed messages; subscription filters enforce scope checking before delivery.

### 4.3 Theory Solvers

- **Simplex (QF_LIA / QF_UFLIA):** Dutertre–de Moura incremental simplex with branch-and-bound for integrality. Ackermann encoding for UF.
- **Congruence closure (QF_UF / QF_UFLIA):** Incremental union-find with explanation generation.
- **Difference logic (QF_IDL / QF_RDL):** Incremental Bellman-Ford.

### 4.4 Sharing Policy

Empirically tuned policy for which messages to broadcast and at what frequency. Backbone inferences are always shared. Theory lemmas above a size threshold are dropped.

---

## 5. Evaluation

*This is Contribution 3: empirical ablation.*

### 5.1 Setup

Hardware, SMT-LIB benchmark selection, comparison with Z3.

### 5.2 Overall Results

Table: PAR-2 scores on QF_LIA, QF_UFLIA, QF_IDL, QF_UF vs. Z3.

### 5.3 Ablation Study

Table: AKX variants (no sharing / lemmas only / backbone only / hints only / full AKX) on each logic. Shows which knowledge type drives the improvement.

### 5.4 Scaling

Speedup as worker count increases from 1 to N.

---

## 6. Related Work

- Portfolio parallel SAT/SMT (ManySAT, Hordesat, CVC5-parallel)
- Cube-and-conquer (Heule et al.)
- Theory propagation in DPLL(T) (Nieuwenhuis & Oliveras)
- Conflict-driven clause sharing (Audemard & Simon)

---

## 7. Conclusion

AKX provides the first formal framework for typed, assumption-scoped knowledge exchange in parallel SMT. The implementation matches Z3 on key logics and isolates the contribution of each knowledge type. Future work: cube-and-conquer integration, GPU offload for Simplex pivots.

---

## Appendix

### A. Proofs

Full proofs of Theorem 3.3 (soundness) and completeness.

### B. Benchmark Details

Full benchmark list, per-family breakdown.
