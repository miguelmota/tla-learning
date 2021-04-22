---- MODULE waterjugs ----
EXTENDS Integers

VARIABLES small, big

\* 1. filling a jug is a single step
\* 2. no intermediate states.

\* this definition is not part of the spec,
\* removing it doesn't change anything
TypeOK == /\ small \in 0..3
          /\ big \in 0..5

\* the initial state formula,
\* asserts that both jugs are empty
Init == /\ big = 0
        /\ small = 0

FillSmall == /\ small' = 3
             /\ big' = big \* leave big jug unchanged

FillBig == /\ big' = 5
           /\ small' = small

EmptySmall == /\ small' = 0
              /\ big' = big

EmptyBig == /\ big' = 0
            /\ small' = small

SmallToBig == IF big + small =< 5
              THEN /\ big' = big + small \* 1.There is room: empty small
                   /\ small' = 0
              ELSE /\ big' = 5 \* 2.There isn't room: fill big
                   /\ small' = small - (5 - big)
                  \* "AND" is commutative: A ∧ B = B ∧ A
                  \* "=" is also commutative: small' = 0 is equivalent to 0 = small'
                  \* TLC only handles the first equals format however.

BigToSmall == IF big + small =< 3
              THEN /\ small' = big + small
                   /\ big' = 0
              ELSE /\ big' = small - (3 - big)
                   /\ small' = 3

\* the next state formula,
\* describes all permitted steps.
\* it's usually written as F1 \/ F2 \/ ... \/ Fn
\* where each formula Fi allows a different kind of step.
\* the behavior we wrote has 3 kinds of steps:
\* - fill a jug
\* - empty a jug
\* - pour from one jug into the other jug

Next == \/ FillSmall
        \/ FillBig
        \/ EmptySmall
        \/ EmptyBig
        \/ SmallToBig
        \/ BigToSmall

Spec == Init /\ [][Next]_<<big, small>>
NotSolved == big /= 4
====
