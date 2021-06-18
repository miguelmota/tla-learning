# TLA+ Learning

> Some examples and notes while learning [TLA+](https://lamport.azurewebsites.net/tla/tla.html) modeling language.

## Notes

- TLA+
  - Temporal Logic of Actions
  - A logical formism based on simple math to describe systems

- The mathematical model
  - A behavior is a sequence of states
  - A state is an assignment of values to variables
  - The system is described by a formula about behaviors
    - That's true on behaviors that represent possible system execution
    - Usually obtained combining two formulas:
      - _Init_ to describe initial states
      - _Next_ to describe state transitions

Notes from Leslie Lamport Course

Lesson 1

- TLA+ is a language for high-level modeling of digital systems
- TLAPS, is the TLA+ proof system
- Use TLA+ to model criticla parts of digital systems
- Abstract away
  - less critical parts
  - lower-level implementation details
- TLA+ was designed for modeling concurrent and distributed systems
- Can help find and correct design errors
  - errors hard to find by testing
  - before writing any code
- Simplifying by removing details is called _abstraction_
- Only through abstraction can we understand complex systems
- We can't get systems right if we don't understand them
- Precise high-level models are called specifications
- TLA+ can specify algorithms and high-level designs
- You don't get a 10x reduction in code size by better coding,
  you get it by coming to a cleaner architecture
- An architecture is a higher-level specification - higher than the code level.
- We use TLA+ to ensure the systems we build work right
- Working right means satisfying certain properties
- The properties TLA+ can check are conditions on individual executions.
- An execution of a system is represented as a sequence of discrete steps.
- Digital system:
  - We can abstract its continious evolution as a sequence of discrete events.
- We can simulate a concurrent system with a sequential program.
- TLA+ describes a step as a step change.
- An execution is represented as a sequence of states.
- A step is the change from one state to the next.
- TLA+ describes a state as an assignment of values to variables.
- A behavior is a sequence of states
- An execution is represented as a behavior
- We want to specify all possible behaviors of a system
- A state machine is described by:
  1. All possible initial states.
  2. What next states can follow any given state.
- A state machine halts if there is no possible next state.
- In TLA+ a state machine is described by:
  0. What the variables are.
  1. Possible initial values of variables.
  2. A relation between their values in the current state and their possible
    values in the next state.

Lesson 2

- We need precise language to describe state machines
- TLA+ uses ordinary, simple math
- Must replace _AND_ (_&&_) by a mathimatical operator _∧_ (logical AND)
- Must replace _OR_ (_||_) by a mathimatical operator _∨_ (logical OR)
- "_i in {0,1,...,1000}_ is written as _i ∈ 0..1000_ in math
- In TLA+ we don't write instructions for computing something, we're writing a formula relating the values.
- The TLA+ source is in ASCII
- In ASCII, ∧ is typed as _/\\_, ∨ is typed as _\\/_ and ∈ is typed as _\in_
- The _=_ sign in TLA+ means math equality, as in _2 + 2 = 4_
  unlike in most programming languages where it means assignment
- Math is much more expressive than standard programming language
- ∧ and ∨ are commutative, so interchaning groups in sub-formulas yields an equivalent formula.
- The math symbol _≜_ means _equal by definition_. In TLA+ it is written as _==_

Lesson 3

- Deadlock - Execution stopped when it wasn't supposed to.
- Termination - Execution stopped when it was suppose to. Most systems should not stop. The default is for TLC to regard stoppint as deadlock.

Lesson 4

- The best way to get started on a spec is to write a single correct behavior.
- TLA+ has no type declarations.
- Type correctness means all the variables have sensible values.
- We can define a formula that asserts type correctness. This helps readers understand the formula.
- TLC can check that type correctness is valid by checking the formula is always true.
- Names must be defined before they are used.
- A formula that is true in every reachable state is called an _invariant_
- The not equal operator is _≠_ and is written in ASCII as _/=_ or _#_
- _≤_ is _=<_ in TLA+ ASCII
- To keep things simple, use a primed variable _v'_ only in one of these two kinds of formulas:
  - _v' = ..._ and _v' ∈ ..._ where _..._ contains no primed variables
- comment out blocks with _(*_ and _*)_
- _∃_ means _There is exists_ and is writen as _\E_ in ASCII.

Lesson 5

- Use _CONSTANT_ to declare a value that is the same throughout every behavior.
- In TLA+, every value is a set.
- Negation operator in C _!_ is _¬_ in TLA+ and is written as _~_ in ASCII
- TLA+ has two kinds of comments
  - _\*_ an end of line comment"
  -
    ```
    (******************)
    (* boxed comments *)
    (* like this      *)
    (******************)
    ```
- We can add pretty printed seperator lines with _----_ in between statements

Lesson 6

- Records
  - the definition
    - _r ≜ [prof |-> "Fred", num |-> 42]_
      - defines _r_ to be a record with two fields _prof_ and _num_.
      - The values of it's two fields are
        - _r.prof = "Fred"_ and _r.num = 42_
    - Chaning the order of the fields makes no difference
  - TLA+ format is
    - _[prof : {"Fred", "Ted", "Ned"}, num : 0..99]_
      - is the set of all records
        - _[prof |-> ..., num |-> ...]_
      - with _prof_ field in set _{"Fred", "Ted", "Ned"}_ and
        - _num_ field in set _0..99_
    - So _[prof |-> "Ned", num |-> 24]_ is in this set.
  - This record is a function
    - _[prof |-> "Fred", num |-> 42]_
      - is a function _f_ with domain _{"prof", "num"}_
      - such that _f["prof"] = "Fred"_ and _f["num"] = 42_
  - _f.prof_ is an abbreviation for _f["prof"]_
  - This except expression equals the record that is the same as _f_ except it's _prof_ field is the string red
    - _[f EXCEPT !["prof"] = "Red"]_
      - this can be abbreviated as
        - _[f EXCEPT !.prof = "Red"]_
- Subset _⊆_ is written as _\subseteq_ in ASCII and read _is a subset of_
- Union set operator _∪_ is written as _\union_ in ASCII
  _S ∪ T_ is the set of all elements _S_ or _T_ or both
- _UNCHANGED <<value1, value2, value3>>_ is equivalent to
  ```tla
    ^ value1' = value1
    ^ value2' = value2
    ^ value3' = value3
  ```
- Angle brackets _⟨ ⟩_ is written as _<< >>_ in ASCII.
- The expression _<< >>_ is for ordered tuples.
- _Enabling conditions_ should go before any prime action formulas.

Lesson 7

- _CHOOSE v \in S : P_ equals
  - if there is a _v_ in _S_ for which _P_ is true
      - _then_ some such _v_
      - _else_ a completely unspecified value
- In math, any expression equals itself
  - _(CHOOSE i \in 1..99 : TRUE) = (CHOOSE i \in 1..9: TRUE)_
- There is no nondetermism in a mathematical expression.
- _x' \in 1..99_
  - Allows the value of _x_ in the next state to be any number in _1..99_
- _x' = CHOOSE i \in 99 : TRUE_
  - Allows the value of _x_ in the next state to be on particular number
- _M \ {x}_
  - _S \ T_ is the set of elements in _S_ not in _T_
    - e.g.  _(10..20) \ (1..14) = 15..20_
- Two Set constructors
  - _{ v \in S : P}_
    - the subset of _S_ consisting of all _v_ satisfying _P_
      - e.g. _{ n \in Nat : n > 17} = {18,19,20,...}_
        - The set of all natural numbers greater than _17_
  - _{ e : v \in S }_
    - The set of all _e_ for _v_ in _S_
      - e.g. _{ n^2 : n \in Nat} = {0, 1, 4, 9, ...}_
        - The set of all squares of natural numbers
- The _LET_ clause makes the definitions local to the _LET_ expressions.
  - The defined identifiers can only be used in the _LET_ expressions.
- Elements of a symmetry set, or a constant assigned elements of a symmetry set, may not appear in a _CHOOSE_ expression.

Lesson 8

- _P => Q_
  - if _P_ is true, then _Q_ is true
  - the symbol _⇒_ written _=>_ and is read _implies_
- _P => Q_ equals _~Q => ~P_
- In speech, implication asserts _causality_.
- In math, implication asserts only _correlation_.
- A _module-closed_ expression is a TLA+ expression that contains only:
  - identifiers declared locally within it
- A module-closed _formula_ is a boolean-valued module-closed expression.
- A constant expression is a (module-complete) expression that (after expanding all definitions):
  - has no declared variables
  - has no non-constant operators.
    e.g. some non-constant operators are _'_ (prime) and _UNCHANGED_
- The value of a constant expression depends only on the values of the declared constants it contains.
- An assumptionat (_ASSUME_) must be a constant formula.
- A state expression can contain anything a constant expression can as well as declared variables.
- The value of a state expression depends on:
  - The value of declared constants
  - The value of declared variables
- A state expression has a value on a state. A state assigns values to variables.
- A constant expression is a state expression that has the same value on all states.
- An action expression can contain anything a state expression can as well as _'_ (prime) and _UNCHANGED_.
- A state expression has a value on a step (a step is a pair of states).
- A state expression is an action expression whose value on the step _s -> t_ depends only on state _s_.
- An action formula is simply called an action.
- A temporal formula has a boolean value on a sequence of states (_behavior_)
- TLA+ has only boolean-valued temporal expressions.
- Example spec:
  - Initial formula
    - _TPInit_
  - Next-state formula
    - _TPNext_
  - _TPSpec_ should be true on _s1 -> s2 -> s3 -> ... iff_
  - _TPInit_ is true on _s1_
  - _TPNext_ is true on s<sub>i</sub> -> s<sub>i+1</sub> for all _i_
  - _TPInit_ is considered to be an action.
- _⎕_ typed _[]_ in ASCII, is read as _always_. The _always_ operator.
- _⎕TPNext_ - "Always TPNext"
- _TPSpec ≜ TPInit /\ [⎕TPNext]<<v1,v2,v3>>_
  - The specification with
    - Initial formula _Init_
    - Next-state formula _Next_
    - Declared variables _v1,...vn_
  - Is expressed by the temporal formula
    - _Init /\ ⎕[Next]<<v1...,vn>>_
- For a temporal formula TF;
  - _THEOREM TF_
    - asserts that _TF_ is true on every possible behavior.
- _THEOREM TPSpec => []TPTypeOK_
  - Asserts that for every behavior:
    - if _TPSpec_ is true on the bheavior
    - then _[]TPTypeOK_ is true on the behavior (means _TPTypeOK_ is true on every state of the behavior).
  - Asserts that _TPTypeOK_ is an invariant of _TPSpec_.
- _INSTANCE TCCommit_
  - _THEOREM TPSpec => TCSpec_
    - Asserts that for every behavior:
      - if it satisfies _TPSpec_
      - then it satisfies _TCSpec_
- Dpecifications are not programs; they're mathematical formulas.
- A specification does not describe the correct behavior of a system,
  rather it describes a universe in which the system and its environment are
  behaving correctly.
- The spec says nothing about irrelevant parts of the universe.
- _THEOREM TPSpec => TCSpec_
  - This theorem makes sense because both formuals are assertions about the same kinds of behavior.
  - It asserts that every behavior satisfying _TPSpec_ satisfies _TCSpec_.
- Steps that leave all the spec's variables unchanged are called stuttering steps
- Every TLA+ spec allows stuttering steps
- We represent a terminating execution by a behavior ending in an infinite sequence of stuttering steps.
  - The universe keeps going even if the system terminates.
  - All behaviors are infinite sequences of states.
- Specs specify what the system _may_ do.
  - They don't specify what it _must_ do.
  - These are different kinds of requirments and should be specified seperately.

Lesson 9

- Tuples are simply finite sequences
- _<< -3, "xyz", {0,2} >>_ is a sequence of length _3_
- A sequence of length _N_ is a function with domain _1..N_
  - _<< -3, "xyz", {0,2} >>[1] = -3_
  - _<< -3, "xyz", {0,2} >>[2] = "xyz"_
  - _<< -3, "xyz", {0,2} >>[3] = {0,2}_
- The sequence _<<1,4,9,...,N^2>>_ is the function such that
    - _<<1,4,9,...,N^2>>[i] = i^2_
  - for all _i_ in _1..N_
    - This is writen as:
      _[i \In 1..N |-> i^2]_
- _Tail(<<s1,..,sn>>)_ equals _<<s2,...,sn>>_
- _Head(seq) == seq[1]_
- _◦_ (concatenation) written as _\o_ concaneates two sequences
  - _<<3,2,1>> ◦ <<"a","b">> = <<3,2,1,"a","b">>_
- Any non-empty sequence is the concaneation of it's head with it's tail
  - _IF seq # <<>> THEN seq = <<Head(seq)>> \o Tail(seq)_
- The _Append_ operator appends an element to the end of the sequence
  - _Append(seq, e) == seq \o <<e>>_
- The operator _Len_ applied to a sequence equals the sequences' length
  - _Len(seq)_
- The domain of a sequence _seq_ is _1..Len(seq)_
  - _1..0 = {}, which is the domain of <<>>_
- _Seq(S)_ is the set of all sequences with elements in _S_.
  - _Seq({3}) = {<<>>, <<3>>, <<3,3>>, <<3,3,3>>, ...}_ (infinite sequences)
- _Remove(i, seq) == [j \in 1..(Len(seq) - 1) |-> IF j < i THEN seq[j] ELSE seq[j + 1]]_
- _Len(Remove(i, seq)) = Len(seq) -1_

Ron Pressler course notes

Part 1

- TLA+ is like a blueprint when designing a house
- In TLA+ the abstraction/implementation relation is expressed by logical implication: _X ⇒ Y_ is the proposition that _X_ implements _Y_, or conversely that _Y_ abstracts _X_.
- Specifying in TLA+ is ultimately specifying with mathematics. But math doesn't save you from thinking; it just helps you organize your thoughts.
- A signature, which is a set of symbols with a specifiy _arity_ - how many arguments the symbol takes.
  - e.g. _5 (0-ary)_, _= (2-ary)_, _< (2-ary)_, _* (2-ary)_
- Expressions can have _quantifier_, like _\A_ ("for all") and "existential quantifier" _\E_ ("there exists")
- _\A x ..._ means "for all objects s such that ..."
- _\E x ..._ means "there exists an object x such that ..."
- A well-formed expression is called a _term_ (of the language), so the syntax is thought of as the set of all the terms.
- A _formula_ is a boolean-valued expression, either _true_ or _false_.
- Variables that appear in a formula unbound are called _free variables__
- A formula that has no free variables is called a _sentence_ or _closed formula_
- A _model_ is the relationship between the syntax and semantics: a model of a formula is a structure that _satisfies_ it.
- It satisfies it by assigment of values to the variables taht make the formula true (truth is a semantic property).
- _⊨_ or _|=_ in ASCII, is the symbol for _satisfies_, on the left is a structure that make the formula on the right true
- The collection of all models of a formula A forms its _formal semantics_ is written as _[[A]]_
- Examples
  - _[[A∧B]]=[[A]]∩[[B]]_ - the model for _A /\ B_ is the intersection of model A with model B.
  - _[A∨B]]=[[A]]∪[[B]]_ - the model for _A \/ B_ is the union of model A with model B.
  - _[[¬A]]=[[A]]c_ - the model ~A is the complement of the model A
- Ehen working with logic, we work within a specific _logical theory_, which is a set of formulas called _axioms_, taken to be equivalent to TRUE.
- A model of a theory is a structure that satisfies all axioms of the theory; the theory specifies a model.
- Peano axioms - logical theory that characterizes the natural numbers and familiar arithmetic operations
- A logic also hash a _calculus_ a syntactic system for deriving expressions from other expressions, like _natural deduction_.
  - If formula _C_ can be derived by a finite number of application of inference rules from formulas _A_ and _B_, we write _A,B ⊢ C_, and
      say that A and B _prove_ C or _entail_ C, where A and B are the assumptions.
  - If formula _A_ is entaile dby theory's axioms alone without any other assumptions, we write _⊢A_ and say _A_ is a _tautology_
  - If _⊢A_ and _A_ is not an axiom, we say that _A_ is a _theorem_. If we want to prove the theorem _A_, but we havne't yet done so, we call _A_ a _proposition_


## Glossary

- TLC - TLA+ model checker
- TLA+ Toolbox - create specs and run tools on them
- TLAPS - the TLA+ proof system
- Deadlock - Execution stopped when it wasn't supposed to.
- Termination - Execution stopped when it was suppose to.
- The TLA+ syntax for an array valued expression:
  _[ variable ∈ set ↦ expression ]_
  - Example:
    _sqr ≜ [i ∈ 1..42 ↦ i^2]_
      - defines _sqr_ to be an array with index set _1..42_
      - such that _sqr[i] = i^2 for all i in 1..42_
- _↦_ is typed as _|->_ in ASCII
- In Math, we use parentheses for function application instead of brackets.
- in TLA+ we write formulas not programs so we use math terminology,
  - function instead of array, domain instead of index set,
  - however TLA+ uses square brackets for function application to avoid confusing with
  - another way mathemiatics uses paranethesis
- Math and TLA+ allow a function to have any set as its domain, for example, the set of all integers.
- The for all symbol _∀_ is typed as _\A_ in ASCII
- the exponentiation operator is represented by the carat chractor e.g. (_i^2_)
- _≡_ or _⇔_ or _<=>_ is "if-and-only-if" equivalence

## Syntax

- _EXTENDS Integers_ - imports arithmetic operators like _+_ and _.._
- _VARIABLES i, pc_ - Declares identifiers
- _Init_ and _Next_ are convention names used
- _<>[]P_ - a termporal operator that every behaviour must conform to where eventually P becomes true and then always stays true. P may switch between true or false but must be true when program terminates.

## Operators
- _/\\_ is "AND"
- _\\/_ is "OR"
- _~_ is "not" negation
- _->_ is "if-then" implication
- _<=>_ is "if-and-only-if" equivalence
- _i^n_ is exponentiation operator

## Terminology

|A|B|
|-|-|
|Programming|Math|
|Array|Function|
|Index Set|Domain|
|f[e]|f(e)|

## CLI

Compile pluscal program:

```bash
pcal program.tla
```

Run TLA+ program:

```bash
tlc program.tla
```

Generate LaTeX:

```bash
tlatex program.tla
```

Generate PDF from LaTeX:

```bash
pdflatex program.tex
```

## Resources

- http://lamport.azurewebsites.net/video/videos.html
- https://github.com/Disalg-ICS-NJU/tlaplus-lamport-projects
- https://github.com/quux00/PlusCal-Examples
- https://github.com/sanjosh/tlaplus
- https://github.com/lostbearlabs/tiny-tlaplus-examples
- https://github.com/pmer/tla-bin
- https://pron.github.io/tlaplus
- https://pron.github.io/posts/tlaplus_part1
- https://github.com/hwayne/tla-snippets
- https://roscidus.com/blog/blog/2019/01/01/using-tla-plus-to-understand-xen-vchan/
- https://surfingcomplexity.blog/2014/06/04/crossing-the-river-with-tla/
- https://sookocheff.com/post/tlaplus/getting-started-with-tlaplus/
- https://www.binwang.me/2020-10-06-Understand-Liveness-and-Fairness-in-TLA.html
- https://docs.imandra.ai/imandra-docs/notebooks/a-comparison-with-tla-plus/
- https://weblog.cs.uiowa.edu/cs5620f15/PlusCal
- http://lamport.azurewebsites.net/tla/book-02-08-08.pdf
- https://lamport.azurewebsites.net/tla/p-manual.pdf
- https://learntla.com/pluscal/a-simple-spec/
- https://github.com/dgpv/SASwap_TLAplus_spec
- https://jack-vanlightly.com/blog/2019/1/27/building-a-simple-distributed-system-formal-verification
- https://tla.msr-inria.inria.fr/tlatoolbox/doc/model/overview-page.html
- https://link.springer.com/content/pdf/bbm%3A978-1-4842-3829-5%2F1.pdf
- https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.519.6413&rep=rep1&type=pdf
- [Lamport TLA+ Course Lectures](https://www.youtube.com/watch?v=p54W-XOIEF8&list=PLWAv2Etpa7AOAwkreYImYt0gIpOdWQevD&index=3)
- [Leslie Lamport: Thinking Above the Code](https://www.youtube.com/watch?v=-4Yp3j_jk8Q)

## License

[MIT](LICENSE)
