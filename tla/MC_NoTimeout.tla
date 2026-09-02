-------------------------- MODULE MC_NoTimeout ----------------------------
(* Variant of MC with the Timeout action removed.
   Used to verify strong liveness: L5 (propagation), L6 (proof→verdict),
   L7 (eventually all nodes prove UNSAT).

   Without Timeout the only escape from "searching" is ReportUnsat, so TLC
   must verify that the Fairness assumptions drive every node to accumulate
   KEY_CLAUSES and declare UNSAT.

   Run with:
     tlc MC_NoTimeout -config MC_NoTimeout.cfg -workers auto

   Expected result: no violation of Safety, EventuallyAllUnsat,
   KeyClausesPropagateToAll, or ProofLeadsToVerdict.
*)

EXTENDS MC   \* inherits concrete constants (Nodes_val, Clauses_val, …)
             \* and all operators from ReasonMesh via MC's EXTENDS chain

(* Next-state relation without Timeout.
   Every other action is identical to the main Spec. *)
Next_NT ==
    \/ \E n \in Nodes_val, c \in Clauses_val      : LearnClause(n, c)
    \/ \E n \in Nodes_val, c \in HighUtil_val      : BridgeForward(n, c)
    \/ \E src \in Nodes_val, dst \in Nodes_val,
          c \in Clauses_val                        : NetDeliver(src, dst, c)
    \/ \E n \in Nodes_val, c \in Clauses_val       : WorkerImport(n, c)
    \/ \E n \in Nodes_val                          : ReportUnsat(n)
    \/ Done

Spec_NT == Init /\ [][Next_NT]_vars /\ Fairness

=============================================================================
