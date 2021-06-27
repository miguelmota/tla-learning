---- MODULE AlternatingBitSpec ----

EXTENDS Integers
CONSTANTS Data \* The set of values that can be transmitted
VARIABLES AVar, BVar

\* AVar and BVar are <<data, 0 or 1>> pairs
TypeOK == /\ AVar \in Data \X {0,1}
          /\ BVar \in Data \X {0,1}

vars == <<AVar, BVar>>

Init == /\ AVar \in Data \X {1} \* AVar can equal <<any element of Data, 1>>
        /\ BVar = AVar

\* A chooses a new value to send
A == /\ AVar = BVar
     /\ \E d \in Data : AVar' = <<d, 1 - AVar[2]>> \* the complement of AVar[2]
     /\ BVar' = BVar

\* B receives a value
B == /\ AVar # BVar
     /\ BVar' = AVar
     /\ AVar' = AVar

Next == A \/ B


\* Any value being sent by A is eventually received by B.
\* \A v \in Data \X {0, 1} : (AVar = v) ~> (BVar = v)

\* is enabled iff
\* /\ AVar = BVar  /\ Data # {}

\* Formula _Spec_ asserts what _may_ happen.
\* Spec == Init /\ [][Next]_vars

\* Asserts that a behavior keeps taking Next steps as long as Next is enabled (not in a deadlocked/terminated state), which means it keeps sending and receiving values forever.
FairSpec == Init /\ [][Next]_vars /\ WF_vars(Next)
====

