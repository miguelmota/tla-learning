---- MODULE tcommit ----
\* disable deadlock check when running.
\* tlc -deadlock tcommit.tla

\* wedding is replaced by database transaction,
\* the processes are called "resource managers".
\* The transaction can either commit or abort.
\* The transaction can commit only if all resource
\* manager are prepared to commit.
\* The transaction must abort if any resource manager
\* wants to abort.

\* The constant RM represents the set of all RMs.
CONSTANT RM

\* the 4 possible states of a resource manager:
\*      working
\*         |
\*      prepared
\*       /     \
\*  committed aborted

VARIABLE rmState

\* The set of all arrays indexed by elements of RM
TCTypeOK == rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

\* The array with index set RM such that
\* [r ∈ RM ↦ "working"][rm] = "working"
\* for all rm in RM
TCInit == rmState = [rm \in RM |-> "working"]

canCommit == \A rm \in RM : rmState[rm] \in {"prepared", "commited"}
notCommitted == \A rm \in RM: rmState[rm] # "commited"

Prepare(rm) == /\ rmState[rm] = "working"
              \* /\ rmState' = [s \in RM |-> IF s = r THEN "prepared" ELSE rmState[s]]
              /\ rmState' = [rmState EXCEPT ![rm] = "prepared"] \* same as above statement

Decide(rm) == \/ /\ rmState[rm] = "prepared"
                /\ canCommit
                /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
             \* this is our second disjunction
             \/ /\ rmState[rm] \in {"working", "prepared"}
                /\ notCommitted
                /\ rmState' = [rmState EXCEPT ![rm] = "aborted"] \* the state of r changes to aborted, while all other RMs stay the same

\* If RM = {"r1", "r2", "r3", "r4"}
\* then this formula equals the disjunction of the 4 formulas we get
\* by substituting in the subformula each of those 4 elements of rm
\* ∨ Prepare("r1") ∨ Decide("r1")
\* ∨ Prepare("r2") ∨ Decide("r2")
\* ∨ Prepare("r3") ∨ Decide("r3")
\* ∨ Prepare("r4") ∨ Decide("r4")

\* The 'exists' "\E" declares r to be local to the formula,
\* so r can be named anything


\* ∀ r ∈ RM : Prepare(r) ∨ Decide(r)
\* For all r in RM, this subformula is true

\* If RM = {"r1", "r2", "r3", "r4"}
\* then the for all formula equals the conjunction of the 4 formulas
\* ∧ Prepare("r1") ∨ Decide("r1")
\* ∧ Prepare("r2") ∨ Decide("r2")
\* ∧ Prepare("r3") ∨ Decide("r3")
\* ∧ Prepare("r4") ∨ Decide("r4")

\* TCNext ≜ ∃r ∈ : Prepare(r) ∨ Decide(r)
\* This formula is true if and only if there exists r in RM,
\* for which this subformula (after colon) is true
TCNext == \E rm \in RM : Prepare(rm) \/ Decide(rm)

\* it's impossible for one RM to have aborted,
\* and another RM to have committed
TCConsistent == \A rm1, rm2 \in RM : ~ /\ rmState[rm1] = "aborted"
                                       /\ rmState[rm2] = "commited"

Spec == TCInit /\ [][TCNext]_<<rmState>>
====
