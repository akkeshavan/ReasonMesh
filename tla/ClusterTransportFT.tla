-------------------------- MODULE ClusterTransportFT --------------------------
\* Fault-tolerant extension of ClusterTransport.
\*
\* Adds worker timeouts and cube retry logic.  A worker that stalls
\* transitions to TimedOut; the coordinator reassigns its cube.
\* A cube exhausting MaxRetries is Abandoned.  Once all cubes are
\* resolved or abandoned the protocol terminates — with result "Unknown"
\* if some cubes were abandoned without a SAT witness.

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    Workers,    \* set of worker node IDs
    Cubes,      \* set of cube IDs
    SatCubes,   \* subset of Cubes with ground-truth answer SAT
    UnsatCubes, \* subset of Cubes with ground-truth answer UNSAT
    MaxRetries  \* max reassignments per cube before abandonment

ASSUME Workers    # {}
ASSUME Cubes      # {}
ASSUME Workers    \cap Cubes      = {}
ASSUME SatCubes   \cup UnsatCubes = Cubes
ASSUME SatCubes   \cap UnsatCubes = {}
ASSUME MaxRetries \in Nat /\ MaxRetries >= 1

NULL == CHOOSE x : x \notin (Workers \cup Cubes)

(* ---------------------------------------------------------------------- *)
(* State variables                                                          *)
(* ---------------------------------------------------------------------- *)

VARIABLES
    cubeStatus,    \* [Cubes -> {"Pending","Assigned","Sat","Unsat","Abandoned"}]
    assignment,    \* [Cubes -> Workers \cup {NULL}]
    workerStatus,  \* [Workers -> {"Idle","Solving"}]
    workerCube,    \* [Workers -> Cubes \cup {NULL}]
    retries,       \* [Cubes -> 0..MaxRetries]
    result         \* "Pending"|"Sat"|"Unsat"|"GaveUp"

vars == <<cubeStatus, assignment, workerStatus, workerCube, retries, result>>

Terminal == result \in {"Sat","Unsat","GaveUp"}

(* ---------------------------------------------------------------------- *)
(* Initial state                                                            *)
(* ---------------------------------------------------------------------- *)

Init ==
    /\ cubeStatus   = [c \in Cubes   |-> "Pending"]
    /\ assignment   = [c \in Cubes   |-> NULL]
    /\ workerStatus = [w \in Workers |-> "Idle"]
    /\ workerCube   = [w \in Workers |-> NULL]
    /\ retries      = [c \in Cubes   |-> 0]
    /\ result = "Pending"

(* ---------------------------------------------------------------------- *)
(* Actions                                                                  *)
(* ---------------------------------------------------------------------- *)

Assign(w, c) ==
    /\ ~Terminal
    /\ workerStatus[w] = "Idle"
    /\ cubeStatus[c]   = "Pending"
    /\ cubeStatus'   = [cubeStatus   EXCEPT ![c] = "Assigned"]
    /\ assignment'   = [assignment   EXCEPT ![c] = w]
    /\ workerStatus' = [workerStatus EXCEPT ![w] = "Solving"]
    /\ workerCube'   = [workerCube   EXCEPT ![w] = c]
    /\ UNCHANGED <<retries, result>>

SolveSat(w) ==
    /\ workerStatus[w] = "Solving"
    /\ workerCube[w] \in SatCubes
    /\ LET c == workerCube[w] IN
        /\ cubeStatus'   = [cubeStatus   EXCEPT ![c] = "Sat"]
        /\ assignment'   = [assignment   EXCEPT ![c] = NULL]
        /\ workerStatus' = [workerStatus EXCEPT ![w] = "Idle"]
        /\ workerCube'   = [workerCube   EXCEPT ![w] = NULL]
        /\ result' = "Sat"
        /\ UNCHANGED retries

SolveUnsat(w) ==
    /\ workerStatus[w] = "Solving"
    /\ workerCube[w] \in UnsatCubes
    /\ LET c        == workerCube[w]
           newCS     == [cubeStatus EXCEPT ![c] = "Unsat"]
           allDone   == \A d \in Cubes : newCS[d] \in {"Sat","Unsat","Abandoned"}
           anySat    == \E d \in Cubes : newCS[d] = "Sat"
           allUnsat  == \A d \in Cubes : newCS[d] = "Unsat"
       IN
        /\ cubeStatus'   = newCS
        /\ assignment'   = [assignment   EXCEPT ![c] = NULL]
        /\ workerStatus' = [workerStatus EXCEPT ![w] = "Idle"]
        /\ workerCube'   = [workerCube   EXCEPT ![w] = NULL]
        /\ result' = IF ~allDone   THEN result
                     ELSE IF anySat   THEN "Sat"
                     ELSE IF allUnsat THEN "Unsat"
                     ELSE "GaveUp"
        /\ UNCHANGED retries

Cancel(w) ==
    /\ result = "Sat"
    /\ workerStatus[w] = "Solving"
    /\ LET c == workerCube[w] IN
        /\ workerStatus' = [workerStatus EXCEPT ![w] = "Idle"]
        /\ workerCube'   = [workerCube   EXCEPT ![w] = NULL]
        /\ cubeStatus'   = [cubeStatus   EXCEPT ![c] = "Pending"]
        /\ assignment'   = [assignment   EXCEPT ![c] = NULL]
        /\ UNCHANGED <<retries, result>>

\* A worker stalls; coordinator detects and either re-queues or abandons the cube.
Timeout(w) ==
    /\ workerStatus[w] = "Solving"
    /\ ~Terminal
    /\ LET c      == workerCube[w]
           newCS0  == IF retries[c] < MaxRetries
                      THEN [cubeStatus EXCEPT ![c] = "Pending"]
                      ELSE [cubeStatus EXCEPT ![c] = "Abandoned"]
           newR    == IF retries[c] < MaxRetries
                      THEN [retries EXCEPT ![c] = retries[c] + 1]
                      ELSE retries
           allDone == \A d \in Cubes : newCS0[d] \in {"Sat","Unsat","Abandoned"}
           anySat  == \E d \in Cubes : newCS0[d] = "Sat"
           allUnsat == \A d \in Cubes : newCS0[d] = "Unsat"
       IN
        /\ workerStatus' = [workerStatus EXCEPT ![w] = "Idle"]
        /\ workerCube'   = [workerCube   EXCEPT ![w] = NULL]
        /\ assignment'   = [assignment   EXCEPT ![c] = NULL]
        /\ cubeStatus'   = newCS0
        /\ retries'      = newR
        /\ result' = IF ~allDone    THEN result
                     ELSE IF anySat    THEN "Sat"
                     ELSE IF allUnsat  THEN "Unsat"
                     ELSE "GaveUp"

(* ---------------------------------------------------------------------- *)
(* Next-state and fairness                                                  *)
(* ---------------------------------------------------------------------- *)

Next ==
    \/ \E w \in Workers, c \in Cubes : Assign(w, c)
    \/ \E w \in Workers : SolveSat(w)
    \/ \E w \in Workers : SolveUnsat(w)
    \/ \E w \in Workers : Cancel(w)
    \/ \E w \in Workers : Timeout(w)

\* Timeout is NOT given fairness: it may or may not happen (adversarial).
\* Workers that don't time out are still required to eventually finish.
Fairness ==
    /\ \A w \in Workers : \A c \in Cubes : WF_vars(Assign(w, c))
    /\ \A w \in Workers : WF_vars(SolveSat(w))
    /\ \A w \in Workers : WF_vars(SolveUnsat(w))
    /\ \A w \in Workers : WF_vars(Cancel(w))

Spec == Init /\ [][Next]_vars /\ Fairness

(* ---------------------------------------------------------------------- *)
(* Safety invariants                                                        *)
(* ---------------------------------------------------------------------- *)

TypeOK ==
    /\ cubeStatus   \in [Cubes   -> {"Pending","Assigned","Sat","Unsat","Abandoned"}]
    /\ assignment   \in [Cubes   -> Workers \cup {NULL}]
    /\ workerStatus \in [Workers -> {"Idle","Solving"}]
    /\ workerCube   \in [Workers -> Cubes \cup {NULL}]
    /\ retries      \in [Cubes   -> 0..MaxRetries]
    /\ result \in {"Pending","Sat","Unsat","GaveUp"}

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

NoDoubleAssignment ==
    \A w1, w2 \in Workers :
        (w1 # w2 /\ workerStatus[w1] = "Solving" /\ workerStatus[w2] = "Solving")
        => workerCube[w1] # workerCube[w2]

RetriesWithinBound ==
    \A c \in Cubes : retries[c] <= MaxRetries

AbandonedMeansExhausted ==
    \A c \in Cubes : cubeStatus[c] = "Abandoned" => retries[c] = MaxRetries

SatSoundness ==
    result = "Sat" => \E c \in Cubes : cubeStatus[c] = "Sat"

UnsatSoundness ==
    result = "Unsat" => \A c \in Cubes : cubeStatus[c] = "Unsat"

SatCubeSound ==
    \A c \in Cubes : cubeStatus[c] = "Sat" => c \in SatCubes

UnsatCubeSound ==
    \A c \in Cubes : cubeStatus[c] = "Unsat" => c \in UnsatCubes

ResultCorrect ==
    /\ result = "Sat"   => SatCubes # {}
    /\ result = "Unsat" => SatCubes = {}

SolvedCubesStable ==
    [][\A c \in Cubes :
        cubeStatus[c] \in {"Sat","Unsat","Abandoned"} =>
            cubeStatus'[c] = cubeStatus[c]]_cubeStatus

ResultStable ==
    [][Terminal => result' = result]_result

NoDeadlock ==
    ~Terminal =>
        \/ \E w \in Workers : workerStatus[w] = "Solving"
        \/ \E w \in Workers, c \in Cubes :
               workerStatus[w] = "Idle" /\ cubeStatus[c] = "Pending"

(* ---------------------------------------------------------------------- *)
(* Liveness                                                                 *)
(* ---------------------------------------------------------------------- *)

\* L1 — Protocol always terminates (Sat, Unsat, or GaveUp).
EventualTermination == <>(Terminal)

\* L2 — Once SAT found, all workers eventually stop.
EventualCancellation ==
    result = "Sat" ~> \A w \in Workers : workerStatus[w] = "Idle"

\* L4 — Every solving worker eventually finishes or times out.
WorkersEventuallyIdle ==
    \A w \in Workers :
        workerStatus[w] = "Solving" ~> workerStatus[w] = "Idle"

\* L5 — Every assigned cube is eventually resolved or returned.
AssignedCubesEventuallyResolved ==
    \A c \in Cubes :
        cubeStatus[c] = "Assigned" ~> cubeStatus[c] # "Assigned"

\* L6 — If a SAT cube is never abandoned (retries not exhausted), result = Sat.
\* In the FT model Timeout has no fairness so TLC explores both paths (times out
\* or not).  This property holds on paths where the SAT cube is not abandoned;
\* it is intentionally omitted from PROPERTIES to avoid false violations on
\* adversarial timeout paths — EventualTermination covers the general case.
\* SatResultIfPossible ==
\*     SatCubes # {} /\ \A c \in SatCubes : cubeStatus[c] # "Abandoned"
\*     => <>(result = "Sat")

(* ---------------------------------------------------------------------- *)
(* Compound                                                                 *)
(* ---------------------------------------------------------------------- *)

Safety ==
    /\ TypeOK
    /\ AssignmentConsistency
    /\ NoDoubleAssignment
    /\ RetriesWithinBound
    /\ AbandonedMeansExhausted
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
