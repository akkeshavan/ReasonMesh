--------------------------------- MODULE MC ---------------------------------
(* Concrete model for TLC safety + weak liveness checking.
   Timeout is enabled; checks I1-I5, L1-L4.

   Model size:
     2 nodes  × 3 clauses  = small enough for TLC to explore in seconds.
     c3 is high-utility but NOT a key clause — tests that non-key clauses
     also propagate correctly without triggering a spurious UNSAT verdict.

   Run with:
     tlc MC -config MC.cfg -workers auto

   Expected result: no violation of Safety, EventualTermination, or
   ConvergentTermination.  TLC will report a state count and "No error found."
*)

EXTENDS ReasonMesh

\* Concrete node identifiers (strings serve as model values here)
Nodes_val      == {"n1", "n2"}
Clauses_val    == {"c1", "c2", "c3"}
KeyClauses_val == {"c1", "c2"}        \* c1 and c2 together prove UNSAT
HighUtil_val   == {"c1", "c2", "c3"} \* all 3 are high-utility; c3 is bonus

=============================================================================
