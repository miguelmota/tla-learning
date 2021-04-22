--- MODULE tendermint ----
CONSTANT AllNodes
VARIABLES blockchain, Faulty

Init ==
  /\ \E NVS \in SUBSET AllNodes:
        blockchain := << [
          height |-> 1,
          time |-> 0,
          VS |-> AllNodes
          NextVS |-> NVS
          lastCommit |-> {},
        ] >>
  /\ Faulty := {}

Next ==
  \/ OneMoreFault
  \/ AddBlock

OneMoreFault ==
  /\ \E n \in AllNodes \ Faulty:
    Faulty' := { n } \union Faulty
  /\ UNCHANGED blockchain

\* SPEC IS UNFINISHED!

\* https://www.youtube.com/watch?v=K2o8znf384w
