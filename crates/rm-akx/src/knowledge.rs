use crate::literal::Literal;
use serde::{Deserialize, Serialize};
use smallvec::SmallVec;

/// Monotonically increasing identifier for a knowledge object within a run.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Serialize, Deserialize)]
pub struct KnowledgeId(pub u64);

/// Opaque reference into a proof store.
#[derive(Clone, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub struct ProofRef(pub u64);

/// Routing scope: how far a knowledge object is permitted to travel.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Serialize, Deserialize)]
pub enum Scope {
    /// Stays within the producing worker's thread.
    Local,
    /// Shared within a single OS process.
    Process,
    /// Shared within a single cluster node.
    Node,
    /// Shared across the whole cluster.
    Global,
}

/// Trust classification for UNSAT closure eligibility.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub enum TrustLevel {
    /// Produced by a verified complete reasoner; may participate in UNSAT closure.
    Trusted,
    /// Produced by an incomplete/experimental reasoner; requires validation before use.
    Proposal,
    /// Branching/scheduling hint only; never used for soundness-critical decisions.
    Hint,
}

// ---------------------------------------------------------------------------
// Per-kind payloads
// ---------------------------------------------------------------------------

/// Assumptions are stored as a sorted SmallVec of literals.
/// Up to 8 literals fit without heap allocation (covers most learned clauses).
pub type AssumptionSet = SmallVec<[Literal; 8]>;

/// Clause knowledge: a disjunction of literals that is valid under `assumptions`.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ClauseKnowledge {
    /// Literals of the clause, in canonical (sorted) order.
    pub literals: SmallVec<[Literal; 8]>,
    /// LBD (Literal Block Distance) score at derivation time.
    pub lbd: u32,
}

/// Theory lemma: a logical consequence valid under given theory context.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TheoryLemma {
    /// Encoded conclusion (theory-specific; opaque outside the theory crate).
    pub conclusion_bytes: Vec<u8>,
    /// Human-readable tag for telemetry (e.g., "euf_congruence", "arith_bound").
    pub theory_tag: String,
}

/// Arithmetic or bit-vector bound on a term.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BoundKnowledge {
    /// Term identifier (from rm-ir term DAG).
    pub term_id: u64,
    pub kind: BoundKind,
    /// Encoded value (interpretation is theory-specific).
    pub value_bytes: Vec<u8>,
}

#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
pub enum BoundKind {
    LessEq,
    GreaterEq,
    Equal,
    NotEqual,
}

/// A set of assumptions forming a sub-problem.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CubeKnowledge {
    pub literals: SmallVec<[Literal; 16]>,
}

/// A set of literals that are jointly inconsistent under the current theory.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ConflictKnowledge {
    pub core: SmallVec<[Literal; 8]>,
    pub theory_tag: String,
}

/// A partial satisfying assignment, proposed by an incomplete worker.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ModelFragment {
    /// Variable → bool assignments. Sparse: may not cover all variables.
    pub assignments: Vec<(u32, bool)>,
}

/// A fragment of a proof derivation.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ProofFragment {
    pub kind: ProofFragmentKind,
    pub bytes: Vec<u8>,
}

#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
pub enum ProofFragmentKind {
    Resolution,
    TheoryCertificate,
    ModelCheck,
}

/// Heuristic scoring hint for branching or routing.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct HeuristicHint {
    /// Variable → score pairs, highest first.
    pub scores: Vec<(u32, f32)>,
    pub source_tag: String,
}

// ---------------------------------------------------------------------------
// Knowledge kind discriminant (for routing/filtering without deserializing)
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Serialize, Deserialize)]
pub enum KnowledgeKindTag {
    Clause,
    TheoryLemma,
    Bound,
    Cube,
    Conflict,
    ModelFragment,
    ProofFragment,
    HeuristicHint,
}

// ---------------------------------------------------------------------------
// The knowledge object
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum KnowledgeKind {
    Clause(ClauseKnowledge),
    TheoryLemma(TheoryLemma),
    Bound(BoundKnowledge),
    Cube(CubeKnowledge),
    Conflict(ConflictKnowledge),
    ModelFragment(ModelFragment),
    ProofFragment(ProofFragment),
    HeuristicHint(HeuristicHint),
}

impl KnowledgeKind {
    pub fn tag(&self) -> KnowledgeKindTag {
        match self {
            Self::Clause(_) => KnowledgeKindTag::Clause,
            Self::TheoryLemma(_) => KnowledgeKindTag::TheoryLemma,
            Self::Bound(_) => KnowledgeKindTag::Bound,
            Self::Cube(_) => KnowledgeKindTag::Cube,
            Self::Conflict(_) => KnowledgeKindTag::Conflict,
            Self::ModelFragment(_) => KnowledgeKindTag::ModelFragment,
            Self::ProofFragment(_) => KnowledgeKindTag::ProofFragment,
            Self::HeuristicHint(_) => KnowledgeKindTag::HeuristicHint,
        }
    }
}

/// A complete AKX knowledge object.
///
/// Validity obligation: `F ∧ assumptions ⊨ conclusion`
/// where F is the original problem formula (globally fixed).
///
/// Unconditional knowledge has `assumptions = []`.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct KnowledgeObject {
    pub id: KnowledgeId,
    pub kind: KnowledgeKind,
    /// Sorted assumption literals under which `kind` was derived.
    /// Empty means the conclusion is unconditional (valid for the whole problem).
    pub assumptions: AssumptionSet,
    pub scope: Scope,
    pub trust: TrustLevel,
    /// Utility estimate [0.0, 1.0]; higher = more likely to be useful.
    pub utility: f32,
    pub proof_ref: Option<ProofRef>,
    /// ID of the worker that produced this object.
    pub source: u32,
}

impl KnowledgeObject {
    /// True if this is an unconditional consequence.
    pub fn is_unconditional(&self) -> bool {
        self.assumptions.is_empty()
    }

    /// The Scope required to share this object one level up the hierarchy.
    pub fn promoted_scope(&self) -> Option<Scope> {
        match self.scope {
            Scope::Local => Some(Scope::Process),
            Scope::Process => Some(Scope::Node),
            Scope::Node => Some(Scope::Global),
            Scope::Global => None,
        }
    }
}

// ---------------------------------------------------------------------------
// Canonical hash for deduplication
// ---------------------------------------------------------------------------

/// Compute a deduplication key for a knowledge object.
///
/// Two objects are considered duplicates iff they have the same tag,
/// the same canonical conclusion bytes, and the same sorted assumption set.
/// An unconditional version of a conclusion supersedes all conditional versions.
pub fn canonical_key(obj: &KnowledgeObject) -> u64 {
    use rustc_hash::FxHasher;
    use std::hash::{Hash, Hasher};

    let mut h = FxHasher::default();
    obj.kind.tag().hash(&mut h);
    // Hash assumptions (already required to be sorted at construction).
    for lit in &obj.assumptions {
        lit.raw().hash(&mut h);
    }
    hash_conclusion_body(&mut h, obj.id, &obj.kind);
    h.finish()
}

/// Compute a key for just the conclusion (kind + canonical form), ignoring
/// the assumption set.
///
/// Used by the bus (§12.4): an unconditional version of a conclusion
/// supersedes all conditional versions of the *same conclusion*, so routing
/// and buffering need to compare conclusions independent of assumptions.
pub fn conclusion_key(obj: &KnowledgeObject) -> u64 {
    use rustc_hash::FxHasher;
    use std::hash::Hasher;

    let mut h = FxHasher::default();
    hash_conclusion_body(&mut h, obj.id, &obj.kind);
    h.finish()
}

/// Hash the knowledge kind tag and the canonical conclusion form (no
/// assumptions). Shared by `canonical_key` and `conclusion_key`.
fn hash_conclusion_body<H: std::hash::Hasher>(h: &mut H, id: KnowledgeId, kind: &KnowledgeKind) {
    use std::hash::Hash;
    kind.tag().hash(h);
    match kind {
        KnowledgeKind::Clause(c) => {
            for lit in &c.literals {
                lit.raw().hash(h);
            }
        }
        KnowledgeKind::Bound(b) => {
            b.term_id.hash(h);
            b.value_bytes.hash(h);
        }
        KnowledgeKind::Cube(c) => {
            for lit in &c.literals {
                lit.raw().hash(h);
            }
        }
        KnowledgeKind::Conflict(c) => {
            for lit in &c.core {
                lit.raw().hash(h);
            }
        }
        // For opaque kinds, hash the raw bytes.
        KnowledgeKind::TheoryLemma(t) => t.conclusion_bytes.hash(h),
        KnowledgeKind::ModelFragment(m) => {
            for (v, b) in &m.assignments {
                v.hash(h);
                b.hash(h);
            }
        }
        KnowledgeKind::ProofFragment(p) => p.bytes.hash(h),
        KnowledgeKind::HeuristicHint(_) => {
            // Hints are not deduplicated by content; each is fresh, so key on
            // the id to keep them distinct (and never superseded).
            id.0.hash(h);
        }
    }
}
