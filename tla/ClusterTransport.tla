---------------------------- MODULE ClusterTransport ----------------------------
\* Specification of the ReasonMesh cluster transport protocol.
\*
\* A coordinator splits a SAT/SMT problem into independent sub-problems
\* called "cubes" and distributes them to worker nodes over AKX/TCP.
\* Each worker solves its cube independently.  The original problem is SAT
\* iff any one cube is SAT; UNSAT iff every cube is UNSAT.
\* When a SAT result is found the coordinator cancels all remaining workers.
\*
\* Ground truth is encoded as two disjoint sets SatCubes / UnsatCubes so
\* TLC can enumerate them directly from the config file.
\*
\* This spec models the happy path (no worker failures).
\* See ClusterTransportFT for the fault-tolerant extension with timeouts.

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    Workers,    \* set of worker node IDs,  e.g. {"w1","w2"}
    Cubes,      \* set of cube IDs,          e.g. {"c1","c2","c3"}
    SatCubes,   \* subset of Cubes whose ground-truth answer is SAT
    UnsatCubes  \* subset of Cubes whose ground-truth answer is UNSAT

ASSUME Workers  # {}
ASSUME Cubes    # {}
ASSUME Workers  \cap Cubes    = {}
ASSUME SatCubes \cup UnsatCubes = Cubes
ASSUME SatCubes \cap UnsatCubes = {}

NULL == CHOOSE x : x \notin (Workers \cup Cubes)

(* ---------------------------------------------------------------------- *)
(* State variables                                                          *)
(* ---------------------------------------------------------------------- *)

VARIABLES
    cubeStatus,    \* [Cubes   -> {"Pending","Assigned","Sat","Unsat"}]
    assignment,    \* [Cubes   -> Workers \cup {NULL}]
    workerStatus,  \* [Workers -> {"Idle","Solving"}]
    workerCube,    \* [Workers -> Cubes \cup {NULL}]
    result         \* "Unknown" | "Sat" | "Unsat"

vars == <<cubeStatus, assignment, workerStatus, workerCube, result>>

(* ---------------------------------------------------------------------- *)
(* Initial state                                                            *)
(* ---------------------------------------------------------------------- *)

Init ==
    /\ cubeStatus   = [c \in Cubes   |-> "Pending"]
    /\ assignment   = [c \in Cubes   |-> NULL]
    /\ workerStatus = [w \in Workers |-> "Idle"]
    /\ workerCube   = [w \in Workers |-> NULL]
    /\ result = "Unknown"

(* ---------------------------------------------------------------------- *)
(* Actions                                                                  *)
(* ---------------------------------------------------------------------- *)

\* Coordinator assigns a pending cube to an idle worker.
\* No new assignments once the result is known.
Assign(w, c) ==
    /\ result          = "Unknown"
    /\ workerStatus[w] = "Idle"
    /\ cubeStatus[c]   = "Pending"
    /\ cubeStatus'   = [cubeStatus   EXCEPT ![c] = "Assigned"]
    /\ assignment'   = [assignment   EXCEPT ![c] = w]
    /\ workerStatus' = [workerStatus EXCEPT ![w] = "Solving"]
    /\ workerCube'   = [workerCube   EXCEPT ![w] = c]
    /\ UNCHANGED result

\* Worker finishes and reports SAT (only if cube is in SatCubes).
SolveSat(w) ==
    /\ workerStatus[w] = "Solving"
    /\ workerCube[w] \in SatCubes
    /\ LET c == workerCube[w] IN
        /\ cubeStatus'   = [cubeStatus   EXCEPT ![c] = "Sat"]
        /\ assignment'   = [assignment   EXCEPT ![c] = NULL]
        /\ workerStatus' = [workerStatus EXCEPT ![w] = "Idle"]
        /\ workerCube'   = [workerCube   EXCEPT ![w] = NULL]
        /\ result' = "Sat"

\* Worker finishes and reports UNSAT (only if cube is in UnsatCubes).
\* Sets global result to Unsat only when every cube is resolved as Unsat.
SolveUnsat(w) ==
    /\ workerStatus[w] = "Solving"
    /\ workerCube[w] \in UnsatCubes
    /\ LET c         == workerCube[w]
           newStatus  == [cubeStatus EXCEPT ![c] = "Unsat"]
           allUnsat   == \A d \in Cubes : newStatus[d] = "Unsat"
       IN
        /\ cubeStatus'   = newStatus
        /\ assignment'   = [assignment   EXCEPT ![c] = NULL]
        /\ workerStatus' = [workerStatus EXCEPT ![w] = "Idle"]
        /\ workerCube'   = [workerCube   EXCEPT ![w] = NULL]
        /\ result' = IF allUnsat THEN "Unsat" ELSE result

\* Coordinator cancels a worker still solving after SAT was found.
Cancel(w) ==
    /\ result          = "Sat"
    /\ workerStatus[w] = "Solving"
    /\ LET c == workerCube[w] IN
        /\ workerStatus' = [workerStatus EXCEPT ![w] = "Idle"]
        /\ workerCube'   = [workerCube   EXCEPT ![w] = NULL]
        /\ cubeStatus'   = [cubeStatus   EXCEPT ![c] = "Pending"]
        /\ assignment'   = [assignment   EXCEPT ![c] = NULL]
        /\ UNCHANGED result

(* ---------------------------------------------------------------------- *)
(* Next-state and fairness                                                  *)
(* ---------------------------------------------------------------------- *)

Next ==
    \/ \E w \in Workers, c \in Cubes : Assign(w, c)
    \/ \E w \in Workers : SolveSat(w)
    \/ \E w \in Workers : SolveUnsat(w)
    \/ \E w \in Workers : Cancel(w)

Fairness ==
    /\ \A w \in Workers : \A c \in Cubes : WF_vars(Assign(w, c))
    /\ \A w \in Workers : WF_vars(SolveSat(w))
    /\ \A w \in Workers : WF_vars(SolveUnsat(w))
    /\ \A w \in Workers : WF_vars(Cancel(w))

Spec == Init /\ [][Next]_vars /\ Fairness

(* ---------------------------------------------------------------------- *)
(* Safety invariants                                                        *)
(* ---------------------------------------------------------------------- *)

\* I1 — TypeOK
TypeOK ==
    /\ cubeStatus   \in [Cubes   -> {"Pending","Assigned","Sat","Unsat"}]
    /\ assignment   \in [Cubes   -> Workers \cup {NULL}]
    /\ workerStatus \in [Workers -> {"Idle","Solving"}]
    /\ workerCube   \in [Workers -> Cubes \cup {NULL}]
    /\ result \in {"Unknown","Sat","Unsat"}

\* I2 — AssignmentConsistency
\* cubeStatus, assignment, workerStatus, workerCube are mutually consistent.
AssignmentConsistency ==
    /\ \A c \in Cubes :
           cubeStatus[c] = "Assigned" =>
               /\ assignment[c] \in Workers
               /\ workerStatus[assignment[c]] = "Solving"
               /\ workerCube[assignment[c]] = c
    /\ \A c \in Cubes :
           cubeStatus[c] # "Assigned" => assignment[c] = NULL
    /\ \A w \in Workers :
           workerStatus[w] = "Solving" =>
               /\ workerCube[w] \in Cubes
               /\ cubeStatus[workerCube[w]] = "Assigned"
               /\ assignment[workerCube[w]] = w
    /\ \A w \in Workers :
           workerStatus[w] = "Idle" => workerCube[w] = NULL

\* I3 — NoDoubleAssignment
\* Two workers cannot hold the same cube simultaneously.
NoDoubleAssignment ==
    \A w1, w2 \in Workers :
        (w1 # w2 /\ workerStatus[w1] = "Solving" /\ workerStatus[w2] = "Solving")
        => workerCube[w1] # workerCube[w2]

\* I4 — SatSoundness
\* Declaring SAT requires at least one cube to have been solved as Sat.
SatSoundness ==
    result = "Sat" => \E c \in Cubes : cubeStatus[c] = "Sat"

\* I5 — UnsatSoundness
\* Declaring UNSAT requires every cube to have been solved as Unsat.
UnsatSoundness ==
    result = "Unsat" => \A c \in Cubes : cubeStatus[c] = "Unsat"

\* I6 — ResultStable (action property)
\* Once the result is known it never changes.
ResultStable == [][result # "Unknown" => result' = result]_result

\* I7 — SatCubeSound
\* A cube recorded as Sat must actually be in SatCubes (solver doesn't lie).
SatCubeSound ==
    \A c \in Cubes : cubeStatus[c] = "Sat" => c \in SatCubes

\* I8 — UnsatCubeSound
\* A cube recorded as Unsat must actually be in UnsatCubes.
UnsatCubeSound ==
    \A c \in Cubes : cubeStatus[c] = "Unsat" => c \in UnsatCubes

\* I9 — SolvedCubesStable (action property)
\* A cube that has been solved never reverts to Pending or Assigned.
SolvedCubesStable ==
    [][\A c \in Cubes :
        cubeStatus[c] \in {"Sat","Unsat"} =>
            cubeStatus'[c] = cubeStatus[c]]_cubeStatus

\* I10 — ResultCorrect
\* The global result directly agrees with the ground-truth cube sets.
ResultCorrect ==
    /\ result = "Sat"   => SatCubes # {}
    /\ result = "Unsat" => SatCubes = {}

\* I11 — NoDeadlock
\* With an unknown result the system can always make progress.
NoDeadlock ==
    result = "Unknown" =>
        \/ \E w \in Workers : workerStatus[w] = "Solving"
        \/ \E w \in Workers, c \in Cubes :
               workerStatus[w] = "Idle" /\ cubeStatus[c] = "Pending"

(* ---------------------------------------------------------------------- *)
(* Liveness properties                                                      *)
(* ---------------------------------------------------------------------- *)

\* L1 — EventualResult: the protocol always terminates.
EventualResult == <>(result # "Unknown")

\* L2 — EventualCancellation: once SAT is found all workers stop.
EventualCancellation ==
    (result = "Sat") ~> (\A w \in Workers : workerStatus[w] = "Idle")

\* L4 — ResultMatchesAnswer: result eventually agrees with the ground-truth sets.
ResultMatchesAnswer ==
    /\ SatCubes   # {} => <>(result = "Sat")
    /\ SatCubes   = {} => <>(result = "Unsat")

\* L5 — WorkersEventuallyIdle: every solving worker eventually finishes.
WorkersEventuallyIdle ==
    \A w \in Workers :
        workerStatus[w] = "Solving" ~> workerStatus[w] = "Idle"

\* L6 — AssignedCubesEventuallyResolved: every assigned cube eventually leaves Assigned.
AssignedCubesEventuallyResolved ==
    \A c \in Cubes :
        cubeStatus[c] = "Assigned" ~> cubeStatus[c] # "Assigned"

(* ---------------------------------------------------------------------- *)
(* Compound properties for TLC                                             *)
(* ---------------------------------------------------------------------- *)

Safety ==
    /\ TypeOK
    /\ AssignmentConsistency
    /\ NoDoubleAssignment
    /\ SatSoundness
    /\ UnsatSoundness
    /\ SatCubeSound
    /\ UnsatCubeSound
    /\ ResultCorrect
    /\ NoDeadlock

=============================================================================
\* Modification History
\* Created October 2026 by Anand Kumar Keshavan
================================================================================
