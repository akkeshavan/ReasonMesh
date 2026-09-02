---- MODULE MC_TTrace_1788362569 ----
EXTENDS Sequences, TLCExt, MC, Toolbox, Naturals, TLC

_expression ==
    LET MC_TEExpression == INSTANCE MC_TEExpression
    IN MC_TEExpression!expression
----

_trace ==
    LET MC_TETrace == INSTANCE MC_TETrace
    IN MC_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        learned = ([n1 |-> {}, n2 |-> {"c1"}])
        /\
        export_q = ([n1 |-> {}, n2 |-> {"c1"}])
        /\
        local_q = ([n1 |-> {}, n2 |-> {}])
        /\
        verdict = ([n1 |-> "timeout", n2 |-> "timeout"])
        /\
        in_flight = ([n1 |-> [n1 |-> {}, n2 |-> {}], n2 |-> [n1 |-> {}, n2 |-> {}]])
    )
----

_init ==
    /\ verdict = _TETrace[1].verdict
    /\ learned = _TETrace[1].learned
    /\ export_q = _TETrace[1].export_q
    /\ local_q = _TETrace[1].local_q
    /\ in_flight = _TETrace[1].in_flight
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ verdict  = _TETrace[i].verdict
        /\ verdict' = _TETrace[j].verdict
        /\ learned  = _TETrace[i].learned
        /\ learned' = _TETrace[j].learned
        /\ export_q  = _TETrace[i].export_q
        /\ export_q' = _TETrace[j].export_q
        /\ local_q  = _TETrace[i].local_q
        /\ local_q' = _TETrace[j].local_q
        /\ in_flight  = _TETrace[i].in_flight
        /\ in_flight' = _TETrace[j].in_flight

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("MC_TTrace_1788362569.json", _TETrace)

=============================================================================

 Note that you can extract this module `MC_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `MC_TEExpression.tla` file takes precedence 
  over the module `MC_TEExpression` below).

---- MODULE MC_TEExpression ----
EXTENDS Sequences, TLCExt, MC, Toolbox, Naturals, TLC

expression == 
    [
        \* To hide variables of the `MC` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        verdict |-> verdict
        ,learned |-> learned
        ,export_q |-> export_q
        ,local_q |-> local_q
        ,in_flight |-> in_flight
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_verdictUnchanged |-> verdict = verdict'
        
        \* Format the `verdict` variable as Json value.
        \* ,_verdictJson |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(verdict)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_verdictModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].verdict # _TETrace[s-1].verdict
        \*             THEN 1 + F[s-1] ELSE F[s-1]
        \*     IN F[_TEPosition - 1]
    ]

=============================================================================



Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to uncomment the module below to deserialize the
 trace from a generated binary file.

\*
\*---- MODULE MC_TETrace ----
\*EXTENDS IOUtils, MC, TLC
\*
\*trace == IODeserialize("MC_TTrace_1788362569.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE MC_TETrace ----
EXTENDS MC, TLC

trace == 
    <<
    ([learned |-> [n1 |-> {}, n2 |-> {}],export_q |-> [n1 |-> {}, n2 |-> {}],local_q |-> [n1 |-> {}, n2 |-> {}],verdict |-> [n1 |-> "searching", n2 |-> "searching"],in_flight |-> [n1 |-> [n1 |-> {}, n2 |-> {}], n2 |-> [n1 |-> {}, n2 |-> {}]]]),
    ([learned |-> [n1 |-> {}, n2 |-> {"c1"}],export_q |-> [n1 |-> {}, n2 |-> {"c1"}],local_q |-> [n1 |-> {}, n2 |-> {}],verdict |-> [n1 |-> "searching", n2 |-> "searching"],in_flight |-> [n1 |-> [n1 |-> {}, n2 |-> {}], n2 |-> [n1 |-> {}, n2 |-> {}]]]),
    ([learned |-> [n1 |-> {}, n2 |-> {"c1"}],export_q |-> [n1 |-> {}, n2 |-> {"c1"}],local_q |-> [n1 |-> {}, n2 |-> {}],verdict |-> [n1 |-> "timeout", n2 |-> "searching"],in_flight |-> [n1 |-> [n1 |-> {}, n2 |-> {}], n2 |-> [n1 |-> {}, n2 |-> {}]]]),
    ([learned |-> [n1 |-> {}, n2 |-> {"c1"}],export_q |-> [n1 |-> {}, n2 |-> {"c1"}],local_q |-> [n1 |-> {}, n2 |-> {}],verdict |-> [n1 |-> "timeout", n2 |-> "timeout"],in_flight |-> [n1 |-> [n1 |-> {}, n2 |-> {}], n2 |-> [n1 |-> {}, n2 |-> {}]]])
    >>
----


=============================================================================

---- CONFIG MC_TTrace_1788362569 ----
CONSTANTS
    NODES <- Nodes_val
    CLAUSES <- Clauses_val
    KEY_CLAUSES <- KeyClauses_val
    HIGH_UTILITY <- HighUtil_val

INVARIANT
    _inv

CHECK_DEADLOCK
    \* CHECK_DEADLOCK off because of PROPERTY or INVARIANT above.
    FALSE

INIT
    _init

NEXT
    _next

CONSTANT
    _TETrace <- _trace

ALIAS
    _expression
=============================================================================
\* Generated on Wed Sep 02 20:52:52 IST 2026