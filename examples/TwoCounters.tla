---- MODULE TwoCounters ----
EXTENDS Integers, TLC

CONSTANT C, Limit
VARIABLES counter

Init ==
  counter = [c \in C |-> 0]

Next ==
  \E c \in C:
    /\ counter[c] < Limit
    /\ counter' = [counter EXCEPT ![c] = counter[c] + 1]

AlwaysNonNegative ==
  /\ \A c \in C : counter[c] > -1

AllAtLimit ==
  /\ \A c \in C : counter[c] = Limit

EventuallyAllAtLimit ==
  /\ <>[]AllAtLimit

Spec == Init /\ [][Next]_<<counter>> /\ WF_<<counter>>(Next)
Live == EventuallyAllAtLimit
====
