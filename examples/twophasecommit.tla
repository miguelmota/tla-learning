---- MODULE twophasecommit ----
\* imports the definitions from TCommit into Module TwoPhase
\* INSTANCE tcommit

\* The spec must describe sending messages.
\* it should specify only what's required of message passing.

CONSTANT RM

\* tm = transaction mananger
\* let msgs be the set of messages currently in transit or simpler,
\* let msgs be the set of messages ever sent.
\* A single message can be received by multiple processes.
\* A process can receive the same message multiple times.
VARIABLES rmState, tmState, tmPrepared, msgs

Messages == [type: {"Prepared"}, rm: RM] \union [type: {"Commit", "Abort"}]
\* [type |-> "Prepared", rm |-> r]
\* the above represents a Prepared message sent by r to the TM.

\* {[type |-> "Commit"], [type |-> "Abort]}
\* Each record represents a message sent by the TM to all RMs


TPTypeOK == /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
            /\ tmState \in {"init", "committed", "aborted"}
            /\ tmPrepared \subseteq RM
            /\ msgs \subseteq Messages

TPInit == /\ rmState = [rm \in RM |-> "working"] \* assigns "working" to every RM
          /\ tmState = "init"
          /\ tmPrepared = {}
          /\ msgs = {}

\* describes the receipt of a prepared message from RM _r_ by TM
\* The first two have no primes and  are conditions, called enabling conditions, on the first state of a step.
TMRcvPrepared(rm) == /\ tmState = "init" \* message can only be received when tm state is in init state
                    /\ [type |-> "Prepared", rm |-> rm] \in msgs \* and there is a prepared message from RM _r_ in the set msgs of sent messages
                    /\ tmPrepared' = tmPrepared \union {rm} \* sets new value of tmPrepared to it's current value and set containing element r. It adds r to tmPrepared
                    /\ UNCHANGED <<rmState, tmState, msgs>>

\* allows steps where the TM sends Commit messages to the RMs and sets tmState to "done".
\* The messages are sent by adding [type -> "Commit"] to msgs.
\* The formula is enabled if and only if tmState equals "init" and tmPrepared equals RM.
TMCommit == /\ tmState = "init"
            /\ tmPrepared = RM
            /\ tmState' = "committed"
            /\ msgs' = msgs \union {[type |-> "Commit"]}
            /\ UNCHANGED <<rmState, tmPrepared>>

\* The TM sends Abort messages to the RMs and sets tmState to "done".
\* it is enabled if and only if tmState equals "init".
TMAbort == /\ tmState = "init"
           /\ tmState' = "aborted"
           /\ msgs' = msgs \union {[type |-> "Abort"]}
           /\ UNCHANGED <<rmState, tmPrepared>>

\* RM r sets its state to "prepared and sends a Prepared message to the TM.
\* it is enabled if and only if rmState[r] equals "working"
RMPrepare(rm) == /\ rmState[rm] = "working"
                 /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]
                 /\ msgs' = msgs \union {[type |-> "Prepared", rm |-> rm]}
                 /\ UNCHANGED <<tmState, tmPrepared>>

\* When in its "working" state, RM r can go to the "aborted" state.
\* After r has aborted, no RM can ever commit; and the TM should eventually take a TMAbort step.
\* In practice, r would inform the TM that it has aborted so the TM knows it should abort the transaction.
RMChooseToAbort(rm) == /\ rmState[rm] = "working"
                      /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
                      /\ UNCHANGED <<tmState, tmPrepared, msgs>>

RMRcvCommitMsg(rm) == /\ [type |-> "Commit"] \in msgs
                      /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
                      /\ UNCHANGED <<tmState, tmPrepared, msgs>>

\* RM r receives a "commit" or "abort" message and set its state accordingly.
RMRcvAbortMsg(rm) == /\ [type |-> "Abort"] \in msgs
                     /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
                     /\ UNCHANGED <<tmState, tmPrepared, msgs>>

TPNext == \/ TMCommit \/ TMAbort
          \* existential quanitification over disjunction of these formulas
          \/ \E rm \in RM:
            TMRcvPrepared(rm) \/ RMPrepare(rm) \/ RMChooseToAbort(rm) \/ RMRcvCommitMsg(rm) \/ RMRcvAbortMsg(rm)

Spec == TPInit /\ [][TPNext]_<<rmState, tmState, tmPrepared, msgs>>
====
