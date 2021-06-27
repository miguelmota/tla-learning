---- MODULE AlternatingBit ----

EXTENDS Integers, Sequences
CONSTANTS Data \* The set of values that can be transmitted
VARIABLES AVar, BVar, AtoB, BtoA

ABS == INSTANCE AlternatingBitSpec

vars == <<AVar, BVar, AtoB, BtoA>>

\* AVar and BVar are <<data, 0 or 1>> pairs
TypeOK == /\ AVar \in Data \X {0,1}
          /\ BVar \in Data \X {0,1}
          \* The set of sequences of values A can send.
          \* A sends a message by appending it to the end of AtoB.
          \* B receives the message at the head of AtoB.
          /\ AtoB \in Seq(Data \X {0, 1})
          /\ BtoA \in Seq({0, 1}) \* The sequence of bits

Remove(i, seq) == [j \in 1..(Len(seq) - 1) |-> IF j < i THEN seq[j] ELSE seq[j + 1]]

Init == /\ AVar \in Data \X {1} \* AVar can equal <<any element of Data, 1>>
        /\ BVar = AVar
        \* Channels are initially empty.
        /\ AtoB = {}
        /\ BtoA = {}

\* A sends a message
ASnd == /\ AtoB' = Append(AtoB, AVar)
        /\ UNCHANGED <<AVar, BtoA, BVar>>

\* A receives a message.
ARcv == /\ BtoA # {} \* is enabled only when sequence is not empty.
        /\ IF Head(BtoA) = AVar[2]
          \* non-determistically chose element of Data.
          THEN \E d \in Data:
                AVar' = <<d, 1 - AVar[2]>> \* second element is complement of AVar's bit.
          ELSE AVar' = AVar
        /\ BtoA' = Tail(BtoA)


BSnd == /\ BtoA' = Append(BtoA, BVar[2])
        /\ UNCHANGED <<AVar, BVar, AtoB>>

BRcv == /\ AtoB # {}
        /\ IF Head(AtoB)[2] # BVar[2]
            THEN BVar' = Head(AtoB)
            ELSE BVar' = BVar
        /\ AtoB' = Tail(AtoB)
        /\ UNCHANGED <<AVar, BtoA>>

\* A message is lost.
LoseMsg ==
      \* Remove a message from AtoB.
      /\ \/ /\ \E i \in 1..Len(AtoB):
                AtoB' = Remove(i, AtoB)
            /\ BtoA' = BtoA

      \* Remove a message from BtoA.
          \/ /\ \E i \in 1..Len(BtoA):
                BtoA' = Remove(i, BtoA)
             /\ AtoB' = AtoB
      /\ UNCHANGED <<AVar, BVar>>

Next == /\ \/ ASnd \/ ARcv \/ BSnd \/ BRcv \/ LoseMsg
        /\ Len(AtoB) =< 3
        /\ Len(BtoA) =< 3

Spec == Init /\ [][Next]_vars
FairSpec == Spec /\ SF_vars(ARcv) /\ SF_vars(BRcv) /\ WF_vars(ASnd) /\ WF_vars(BSnd)
\* THEOREM Spec => ABS!Spec
====

