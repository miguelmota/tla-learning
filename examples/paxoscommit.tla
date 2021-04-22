--- MODULE paxoscommit ---
\* Paxos Commit is a fault-tolerant transaction-commit algorithm described in
\* the paper "Consensus on Transaction Commit"

CONSTANTS RM, Acceptor, Majority, Ballot

VARIABLES rmState, aState, msgs

\* The largest element of finite set S of integers,
\* or -1 if S is the empty set
Maximum(S) ==
  IF S = {} THEN -1
    \* ELSE CHOOSE n \in S: n >= every element is S
    ELSE CHOOSE n \in S: \A m \in S : n => m


ASSUME
  /\ Ballot \subseteq Nat \* non-negative integers
  /\ 0 \in Ballot
  \* here "SUBSET Acceptor" means the set of all subsets of Acceptor
  /\ Majority \subseteq SUBSET Acceptor \* Every element of Majority is a subset of the set Acceptor
  \* this asserts that any two elements of Majority have an element in common
  /\ \A MS1, MS2 \in Majority : MSI \cap MS2 # {} \* the intersection of all elements in MS1 and MS2

Message ==
  [type : {"phase1a"}, ins: RM, bal: Ballot \ {0}]
  \cup
  [type : {"phase1b"}, ins: RM, mbal: Ballot, bal: Ballot \cup {-1},
  val:{"prepared", "aborted", "none"}, acc: Acceptor]
  \cup
  [type:{"phase2a"}, ins: RM, bal: Ballot, val: {"prepared", "aborted"}]
  \cup
  [type:{"phase2b"}, acc: Acceptor, ins: RM, bal: Ballot,
    val: {"prepared", "aborted"}]
  \cup
  [type: {"Commit", "Abort"}]

PCTypeOK ==
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  \* here "r \in RM" implies aState[r] is a function with domain Acceptor,
  \* such that "a \in Acceptor" implies aState[r][a] is a record with three fields.
  /\ aState \in [RM -> [Acceptor -> [mbal : Ballot
                                    bal  : Ballot \cup {-1} \* aState[r][a].bal is in Ballot or equals -1
                                     val  : {"prepared", "aborted", "none"}]]]
  /\ msgs \subseteq Messages

Phase2a(bal, r) ==
  /\ ~ \E m \in msgs : /\ m.type = "phase2a"
                       /\ m.bal = bal
                       /\ m.ins = r
  /\ \E MS \in Majority :
    LET mset ==
            {m \in msgs : /\ m.type = "phase1b"}
                          /\ m.ins = r
                          /\ m.mbal = bal
                          /\ m.acc \in MS }
        maxbal ==
            Maximum({m.bal : m \in mset})
        val == IF maxbal = -1
                THEN "aborted"
                ELSE (CHOOSE m \in mset : m.bal == maxbal).val
    IN
      /\ \A ac \in MS : \E m \in mset : m.acc = ac
      /\ Send([type |-> "phase2a", ins |-> r, bal |-> bal, val |-> val])
  /\ UNCHANGED <<rmState, aState>>

Phase1b(acc) ==
  \E m \in msgs :
    /\ m.type = "phase1a"
    /\ aState[m.ins][acc].mbal < m.bal
    /\ aState' = [aState EXCEPT ![m.ins][acc].mbal == m.bal]
    /\ Send([type |-> "phase1b",
             ins  |-> m.bal,
             bal  |-> aState[m.ins][acc].bal,
             val  |-> aState[m.ins][acc].val,
             acc  |-> acc])
    /\ UNCHANGED rmState
====
