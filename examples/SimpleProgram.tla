---- MODULE SimpleProgram ----
EXTENDS Integers
VARIABLES i, pc

Init == pc = "start" /\ i = 0

Pick == \/ /\ pc = "start"
           /\ i' \in 0..1000
           /\ pc' = "middle"

Add1 == \/ /\ pc = "middle"
           /\ i' = i + 1
           /\ pc' = "done"

Next == Pick \/ Add1

Spec == Init /\ [][Next]_<<i,pc>>
====

(*
---- NOTES ----

int i;
void main()
{
  i = someNumber();
  i = i + 1;
}

A possible execution:
  [i:0] -> [i:42] -> [i:43]


- In TLA+ a state machine is described by:
  0. What the variables are.
  1. Possible initial values of variables.
  2. A relation between their values in the current state and their possible
    values in the next state.

Described as state machine:
  0. i
  1. i = 0
  2. no possible next value because the program has terminated

The problem: the value _i_ is only part of the program's state.
The other part of the state: what statement is executed next. This is called _the control state_

to describe as state machine:

              int i;
              void main()
              {
pc = "start"    i = someNumber();
pc = "middle"   i = i + 1;
pc ="done"    }

pc = program control
0. The variables: i, pc
1. initial values: i = 0 and pc ="start"
2.
  if current value of _pc_ equals _"start"_
    then next value of _i_ in _{0,1,...,1000}_
      next value of _pc_ equals _"middle"_
    else if current value of _pc_ equals _"middle"_
      then next value of _i_ equals current value of _i + 1_
        next value of _pc_ equals _"done"_
      else no next values

written in math as
IF pc = "start"
  THEN (i' ∈ 0..1000) ∧
       (pc' = "middle")
  ELSE IF pc = "middle"
        THEN (i' = i + 1) ∧
             (pc' = "done")
        ELSE FALSE

It means: if _pc = "start"_ then formula equals the "then" formula, otherwise it
  equals the "else" formula.

There are two cases when the formula is true:
1. (pc = "start") ∧ A is true
2. (pc = "middle") ∧ B is true

IF pc = "start"
  THEN A
  ELSE IF "pc = "middle
    THEN B
    ELSE FALSE

Let's format it better:

∨
  ∧ pc = "start"
  ∧ i' ∈ 0..100
  ∧ pc' = "middle"
∨
  ∧ pc = "middle"
  ∧ i' = i + 1
  ∧ pc' = done

Initial-state formula: (i = 0) ∧ (pc = "start")

Full SimpleProgram:


Init ≜ (i = 0) ∧ (pc = "start")
Next ≜  ∨
          ∧ pc = "start"
          ∧ i' ∈ 0..100
          ∧ pc' = "middle"
        ∨
          ∧ pc = "middle"
          ∧ i' = i + 1
          ∧ pc' = done
*)
