---------------------------- MODULE ReasonMesh ----------------------------
(* TLA+ specification of the ReasonMesh distributed clause-sharing protocol.

   WHAT IS MODELLED
   ----------------
   We model the AKX network layer: BroadcastBus dual-queue design, bridge
   thread forwarding, TCP delivery, and peer import.  The CDCL search engine
   is abstracted as a nondeterministic oracle — any clause in CLAUSES may be
   learned by any node at any time.  This lets TLC verify the protocol layer
   independently of any particular solver heuristic.

   CONSTANTS
   ---------
   NODES        - set of cluster nodes, e.g. {"n1", "n2"}
   CLAUSES      - universe of abstract clause IDs, e.g. {"c1", "c2", "c3"}
   KEY_CLAUSES  - subset of CLAUSES that together constitute an UNSAT proof
   HIGH_UTILITY - subset of CLAUSES whose LBD <= threshold (bridge forwards these)

   KEY AXIOM:  KEY_CLAUSES ⊆ HIGH_UTILITY
   The proof-critical clauses must be high-utility, otherwise the LBD filter
   in the bridge would silently discard them and the proof could never propagate.

   VARIABLES
   ---------
   learned[n]        - all clauses known to any worker on node n (monotone)
   export_q[n]       - high-utility clauses queued in the BroadcastBus export
                       queue, waiting for the bridge thread to forward them
   in_flight[src][dst] - clauses that src's bridge has published to the NetBus
                         but dst has not yet received (models TCP in-transit)
   local_q[n]        - clauses received from peers via TCP, sitting in the
                       InprocBus waiting for a local worker to import them
   verdict[n]        - "searching" | "unsat" | "timeout"

   See MC.tla and MC.cfg for the TLC model configuration.
   See MC_NoTimeout.tla / MC_NoTimeout.cfg for strong liveness checking.
*)

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    NODES,       \* cluster nodes
    CLAUSES,     \* universe of clause IDs
    KEY_CLAUSES, \* proof-necessary clauses (subset of CLAUSES)
    HIGH_UTILITY \* bridge-eligible clauses (subset of CLAUSES)

ASSUME KEY_CLAUSES  \subseteq CLAUSES
ASSUME HIGH_UTILITY \subseteq CLAUSES
ASSUME KEY_CLAUSES  \subseteq HIGH_UTILITY \* key clauses must cross the network

-----------------------------------------------------------------------------
VARIABLES
    learned,   \* learned[n]     : SUBSET CLAUSES
    export_q,  \* export_q[n]    : SUBSET HIGH_UTILITY
    in_flight, \* in_flight[n][m]: SUBSET CLAUSES  (n -> m channel)
    local_q,   \* local_q[n]     : SUBSET CLAUSES
    verdict    \* verdict[n]     : {"searching","unsat","timeout"}

vars == <<learned, export_q, in_flight, local_q, verdict>>

Verdicts == {"searching", "unsat", "timeout"}

TypeInvariant ==
    /\ learned   \in [NODES -> SUBSET CLAUSES]
    /\ export_q  \in [NODES -> SUBSET CLAUSES]
    /\ in_flight \in [NODES -> [NODES -> SUBSET CLAUSES]]
    /\ local_q   \in [NODES -> SUBSET CLAUSES]
    /\ verdict   \in [NODES -> Verdicts]

-----------------------------------------------------------------------------
(* INITIAL STATE *)

Init ==
    /\ learned   = [n \in NODES |-> {}]
    /\ export_q  = [n \in NODES |-> {}]
    /\ in_flight = [n \in NODES |-> [m \in NODES |-> {}]]
    /\ local_q   = [n \in NODES |-> {}]
    /\ verdict   = [n \in NODES |-> "searching"]

-----------------------------------------------------------------------------
(* ACTIONS *)

(* A CDCL worker on node n derives clause c.
   Written to both the local bus (for same-node workers) and, if c meets
   the utility threshold, to the export queue for the bridge thread. *)
LearnClause(n, c) ==
    /\ verdict[n] = "searching"
    /\ c \notin learned[n]
    /\ learned'  = [learned  EXCEPT ![n] = @ \cup {c}]
    /\ export_q' = [export_q EXCEPT ![n] = @ \cup
                       (IF c \in HIGH_UTILITY THEN {c} ELSE {})]
    /\ UNCHANGED <<in_flight, local_q, verdict>>

(* Bridge thread on n dequeues clause c from the export queue and fans it
   out to every peer simultaneously (one NetBus publish call).
   No verdict guard: the bridge continues draining even after a verdict
   fires (TCP socket is not closed until WorkerPool::shutdown completes).
   Over-approximation is safe — extra forwards don't affect soundness. *)
BridgeForward(n, c) ==
    /\ c \in export_q[n]
    /\ export_q'  = [export_q  EXCEPT ![n] = @ \ {c}]
    /\ in_flight' = [in_flight EXCEPT ![n] =
                        [m \in NODES |-> IF m # n
                                         THEN in_flight[n][m] \cup {c}
                                         ELSE in_flight[n][m]]]
    /\ UNCHANGED <<learned, local_q, verdict>>

(* TCP delivers clause c from src's outbound channel to dst's local queue.
   Models the NetBus reader thread completing one frame read. *)
NetDeliver(src, dst, c) ==
    /\ src # dst
    /\ c \in in_flight[src][dst]
    /\ in_flight' = [in_flight EXCEPT ![src][dst] = @ \ {c}]
    /\ local_q'   = [local_q   EXCEPT ![dst]      = @ \cup {c}]
    /\ UNCHANGED <<learned, export_q, verdict>>

(* Worker on n polls one clause from the InprocBus (local_q) and applies it
   to its solver.  Models the import side of drain_export_import.
   No verdict guard: a node that just reported UNSAT still drains the queue
   before shutting down, and imports after timeout are discarded by the OS
   buffer flush.  Over-approximation does not affect safety invariants
   because learned is monotone and UnsatRequiresProof holds once set. *)
WorkerImport(n, c) ==
    /\ c \in local_q[n]
    /\ learned'  = [learned  EXCEPT ![n] = @ \cup {c}]
    /\ local_q'  = [local_q  EXCEPT ![n] = @ \ {c}]
    /\ UNCHANGED <<export_q, in_flight, verdict>>

(* Worker on n has accumulated the complete proof: KEY_CLAUSES ⊆ learned[n].
   Reports UNSAT.  No fabrication: the guard enforces soundness. *)
ReportUnsat(n) ==
    /\ verdict[n] = "searching"
    /\ KEY_CLAUSES \subseteq learned[n]
    /\ verdict' = [verdict EXCEPT ![n] = "unsat"]
    /\ UNCHANGED <<learned, export_q, in_flight, local_q>>

(* Node n's wall-clock deadline fires before it reaches a verdict.
   Models the timeout_secs parameter in WorkerPool::run.
   When the pool shuts down: the bridge thread exits (export_q flushed),
   TCP connections are closed (in_flight to/from n dropped), and pending
   imports are discarded (local_q cleared).  Learned clauses are kept
   because the solver's in-memory state is read-only at that point. *)
Timeout(n) ==
    /\ verdict[n] = "searching"
    /\ verdict'   = [verdict  EXCEPT ![n] = "timeout"]
    /\ export_q'  = [export_q EXCEPT ![n] = {}]
    /\ local_q'   = [local_q  EXCEPT ![n] = {}]
    /\ in_flight' = [src \in NODES |-> [dst \in NODES |->
                        IF src = n \/ dst = n THEN {} ELSE in_flight[src][dst]]]
    /\ UNCHANGED <<learned>>

(* Terminal stuttering step.
   Once every node has a verdict the system is done.  Modelled as an
   explicit UNCHANGED self-loop so TLC does not flag the final state as
   a deadlock (TLA+ semantics allow stuttering; TLC's deadlock checker
   requires at least one enabled Next disjunct in every state). *)
Done ==
    /\ \A n \in NODES : verdict[n] # "searching"
    /\ UNCHANGED vars

-----------------------------------------------------------------------------
(* NEXT-STATE RELATION *)

Next ==
    \/ \E n \in NODES, c \in CLAUSES      : LearnClause(n, c)
    \/ \E n \in NODES, c \in HIGH_UTILITY : BridgeForward(n, c)
    \/ \E src \in NODES, dst \in NODES, c \in CLAUSES : NetDeliver(src, dst, c)
    \/ \E n \in NODES, c \in CLAUSES      : WorkerImport(n, c)
    \/ \E n \in NODES                     : ReportUnsat(n)
    \/ \E n \in NODES                     : Timeout(n)
    \/ Done

-----------------------------------------------------------------------------
(* FAIRNESS ASSUMPTIONS

   WF_vars(A): if A is continuously enabled it eventually fires.
               Models "the system makes progress whenever it can."
   SF_vars(A): if A is infinitely often enabled it fires infinitely often.
               Used only for LearnClause on key clauses — models that the
               portfolio of CDCL workers is diverse enough that every node
               will eventually derive every key clause independently.

   Together these say: the bridge, network, and import paths don't stall
   permanently, and the CDCL search is productive.  Timeout is NOT given
   fairness here — it can fire at any time (or never).
*)

Fairness ==
    \* Infrastructure: if a clause is queued/in-flight/importable, it moves.
    /\ \A n \in NODES, c \in HIGH_UTILITY :
            WF_vars(BridgeForward(n, c))
    /\ \A src \in NODES, dst \in NODES, c \in CLAUSES :
            WF_vars(NetDeliver(src, dst, c))
    /\ \A n \in NODES, c \in CLAUSES :
            WF_vars(WorkerImport(n, c))
    \* Search: each key clause is eventually derived on every node.
    \* SF (not WF) because CDCL may miss a clause on one pass but revisit it.
    /\ \A n \in NODES, c \in KEY_CLAUSES :
            SF_vars(LearnClause(n, c))
    \* Verdict: once a node has the proof, it will report it.
    /\ \A n \in NODES :
            WF_vars(ReportUnsat(n))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* SAFETY INVARIANTS
   Checked by TLC on every reachable state.  None of these should ever be
   violated; a TLC counterexample would indicate a protocol bug.
*)

(* I1: Type safety — all variables have correct types. *)
TypeOK == TypeInvariant

(* I2: Soundness of UNSAT verdict.
   A node may claim UNSAT only if it has accumulated the full proof.
   This is the soundness direction of the AKX guarantee: verdicts are
   evidence-based, not guessed.
   COUNTEREXAMPLE would mean: ReportUnsat fires without all KEY_CLAUSES. *)
UnsatRequiresProof ==
    \A n \in NODES : verdict[n] = "unsat" => KEY_CLAUSES \subseteq learned[n]

(* I3: Filter integrity.
   Only high-utility clauses may appear in export queues or in-flight channels.
   This verifies the BroadcastBus design: low-LBD clauses written to the export
   queue only when c \in HIGH_UTILITY (see LearnClause guard).
   COUNTEREXAMPLE would mean: a low-utility clause bypassed the filter. *)
FilterIntegrity ==
    /\ \A n \in NODES :
            export_q[n] \subseteq HIGH_UTILITY
    /\ \A src \in NODES, dst \in NODES :
            in_flight[src][dst] \subseteq HIGH_UTILITY

(* I4: Export queue soundness.
   The bridge cannot forward a clause the node has not yet learned.
   Models the "export from outbox only" rule in drain_and_export.
   COUNTEREXAMPLE would mean: a clause appeared in export_q without being learned. *)
ExportQueueSound ==
    \A n \in NODES : export_q[n] \subseteq learned[n]

(* I5: In-flight soundness.
   Clauses in transit were learned by the sender before transmission.
   The network cannot conjure knowledge.
   COUNTEREXAMPLE would mean: in_flight contains a clause the sender never learned. *)
InFlightSound ==
    \A src \in NODES, dst \in NODES : in_flight[src][dst] \subseteq learned[src]

(* Combined invariant for TLC: checking one name is simpler than listing four. *)
Safety ==
    /\ TypeOK
    /\ UnsatRequiresProof
    /\ FilterIntegrity
    /\ ExportQueueSound
    /\ InFlightSound

-----------------------------------------------------------------------------
(* LIVENESS PROPERTIES
   Expressed as temporal formulas (leads-to ~>, eventually <>).
   TLC checks these only when SPECIFICATION includes Fairness.
   Properties L1-L4 hold even with Timeout enabled.
   Properties L5-L7 hold only in MC_NoTimeout (Timeout excluded).
*)

(* L1: Clause forwarding progress.
   Any clause queued for export is eventually removed from the export queue.
   No clause gets stuck in the bridge forever.
   Enabled by WF_vars(BridgeForward). *)
ClausesEventuallyForwarded ==
    \A n \in NODES, c \in HIGH_UTILITY :
        (c \in export_q[n]) ~> (c \notin export_q[n])

(* L2: Network delivery progress.
   Any in-flight clause is eventually delivered to its destination.
   Models TCP reliability (no permanent packet loss).
   Enabled by WF_vars(NetDeliver). *)
ClausesEventuallyDelivered ==
    \A src \in NODES, dst \in NODES, c \in CLAUSES :
        (c \in in_flight[src][dst]) ~> (c \notin in_flight[src][dst])

(* L3: Every node eventually terminates.
   No node stays "searching" forever; it either proves UNSAT or times out.
   Holds with Timeout: Timeout can always fire as an escape hatch. *)
EventualTermination ==
    \A n \in NODES : (verdict[n] = "searching") ~> (verdict[n] # "searching")

(* L4: Convergent termination.
   Once any node proves UNSAT, all other nodes eventually terminate too.
   They either accumulate the same proof via sharing, or timeout.
   This is the "fleet convergence" property: clause sharing means the fleet
   is no slower to terminate than the single fastest node. *)
ConvergentTermination ==
    (\E n \in NODES : verdict[n] = "unsat") ~>
    (\A m \in NODES : verdict[m] # "searching")

(* L5: Key clauses propagate to all nodes.
   Any key clause learned on one node eventually appears in every other node's
   learned set.  This is the central correctness claim of the sharing protocol.
   Only provable WITHOUT Timeout (a timeout before delivery is a counterexample).
   Enabled by WF_vars(BridgeForward + NetDeliver + WorkerImport). *)
KeyClausesPropagateToAll ==
    \A n \in NODES, m \in NODES, c \in KEY_CLAUSES :
        (c \in learned[n]) ~> (c \in learned[m])

(* L6: Having the proof leads to the verdict.
   Once a node has all key clauses it will eventually report UNSAT.
   Combines I2 (necessary) and this property (sufficient): the guard and the
   action are both sides of the same contract.
   Only provable WITHOUT Timeout.
   Enabled by WF_vars(ReportUnsat). *)
ProofLeadsToVerdict ==
    \A n \in NODES :
        (KEY_CLAUSES \subseteq learned[n]) ~> (verdict[n] = "unsat")

(* L7: Eventually the entire fleet agrees on UNSAT.
   The strongest claim: every node eventually reaches "unsat" (not just "timeout").
   Requires: no Timeout fires before key clauses are accumulated.
   Models the ideal cluster run where the problem is solved before deadline.
   Implies L6 and L5 and L3. *)
EventuallyAllUnsat ==
    <>(\A n \in NODES : verdict[n] = "unsat")

=============================================================================
