# TLA+ Learning

> Some examples and notes while learning [TLA+](https://lamport.azurewebsites.net/tla/tla.html) modeling language.

## Notes

TLA+
- Temporal Logic of Actions
- a logical formism based on simple math to describe systems

The mathematical model
- a behavior is a sequence of states
- a state is an assignment of values to variables
- the system is described by a formula about behaviors
  - that's true on behaviors that represent possible system execution
  - usually obtained combining two formulas:
    - _Init_ to describe initial states
    - _Next_ to describe state transitions

lesson 1
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

lesson 2
- We need precise language to describe state machines
- TLA+ uses ordinary, simple math
- Must replace "and" (&&) by a mathimatical operator "∧" (logical AND)
- Must replace "or" (||) by a mathimatical operator "∨" (logical OR)
- "i in {0,1,...,1000}" is written as "i ∈ 0..1000" in math
- In TLA+ we don't write instructions for computing something, we're writing a formula relating the values.
- The TLA+ source is in ASCII
- In ASCII, ∧ is typed as "/\", ∨ is typed as "\/ and ∈ is typed as "\in",
- The "=" sign in TLA+ means math equality, as in 2 + 2 = 4,
  unlike in most programming languages where it means assignment
- Math is much more expressive than standard programming language
- ∧ and ∨ are commutative, so interchaning groups in sub-formulas yields an equivalent formula.
- The math symbol "≜" means "equal by definition". In TLA+ it is written as "=="

lesson 3
- Deadlock - Execution stopped when it wasn't supposed to.
- Termination - Execution stopped when it was suppose to. Most systems should not stop. The default is for TLC to regard stoppint as deadlock.

lesson 4
- The best way to get started on a spec is to write a single correct behavior.
- TLA+ has no type declarations.
- Type correctness means all the variables have sensible values.
- We can define a formula that asserts type correctness. This helps readers understand the formula.
- TLC can check that type correctness is valid by checking the formula is always true.
- Names must be defined before they are used.
- A formula that is true in every reachable state is called an _invariant_
- The equal is written as "/=" or "#", in pretty it is "≠"
- "≤" is "=<" in TLA+ ASCII
- Too keep things simple, use a primed variable v' only in one of these two kinds of formulas:
  - v' = ... and v' ∈ ... where ... contains no primed variables
- comment out blocks with _(*_ and _*)_
- "There is exists" ∃ and writen as "\E" in ASCII

lesson 5
- Use `CONSTANT` to declare a value that is the same throughout every behavior.
- In TLA+, every value is a set.
- negation operator in C "!" is "¬ " in TLA+ and is written as "~" in ASCII
- TLA+ has two kinds of comments
  - "\* an end of line comment"
  -
    (******************)
    (* boxed comments *)
    (* like this      *)
    (******************)
- We can add pretty printed seperator lines with "-------" in between statements

lesson 6
- records -
  the definition
    r ≜ [prof |-> "Fred", num |-> 42]
  defines r to be a record with two fields prof and num.
  The values of it's two fields are
    r.prof = "Fred" and r.num = 42
  Chaning the order of the fields makes no difference
  - TLA+ format is
    [prof : {"Fred", "Ted", "Ned"}, num : 0..99]
    is the set of all records
    [prof |-> ..., num |-> ...]
    with prof field in set {"Fred", "Ted", "Ned"} and
      num field in set 0..99
    So [prof |-> "Ned", num |-> 24] is in this set.
  This record is a function
    [prof |-> "Fred", num |-> 42]
  is a function _f_ with domain {"prof", "num"}
  such that _f["prof"] = "Fred"_ and _f["num"] = 42__
  f.prof is an abbreviation for f["prof"]
  This except expression equals the record that is the same as f except it's prof field is the string red
  [f EXCEPT !["prof"] = "Red"]
  this can be abbreviated as
  [f EXCEPT !.prof = "Red"]
- Subset "⊆" is written as "\subseteq" in ASCII and read "is a subset of"
- Union set operator "∪" is written as "\union" in ASCII
  _S ∪ T_ is the set of all elements S or T or both
- _UNCHANGED <<value1, value2, value3>>_ is equivalent to
  ^ value1' = value1
  ^ value2' = value2
  ^ value3' = value3
- angle brackets "⟨ ⟩" is written as ""<< >>" in ASCII
- the expression "<< >>" is for ordered tuples
- _Enabling conditions_ should go before any prime action formulas.

lesson 7
- CHOOSE v \in S : P equals
  if there is a v in S for which P is true
      then some such v
      else a completely unspecified value
- math, any expression equals itself
  (CHOOSE i \in 1..99 : TRUE) = (CHOOSE i \in 1..9: TRUE)
- There is no nondetermism in a mathematical expression.
- x' \in 1..99
  Allows the value of x in the next state to be any number in 1..99
- x' = CHOOSE i \in 99 : TRUE
  Allows the value of x in the next state to be on particular number
- M \ {x}
  S \ T is the set of elements in S not in T
  Example: (10..20) \ (1..14) = 15..20
- Two Set constructors
  - { v \in S : P}
    - the subset of S consisting of all v satisfying P
      example: { n \in Nat : n > 17} = {18,19,20,...}
        the set of all natural numbers greater than 17
  - { e : v \in S }
    - the set of all e for v in S
      example: { n^2 : n \in Nat} = {0, 1, 4, 9, ...}
        the set of all squares of natural numbers
- The LET clause makes the definitions local to the LET expressions.
  The defined identifiers can only be used in the LET expressions.
- Elements of a symmetry set, or a constant assigned elements of a symmetry set,
may not appear in a CHOOSE expression

lesson 8
- P => Q
  - if P is true, then Q is true
  - the symbol "⇒" written "=>", is read _implies_
- P => Q equals ~Q => ~P
- in speech, implication asserts causality.
- in math, implication asserts only correlation.
- A _module-closed_ expression is a TLA+ expression that contains only:
  - identifiers declared locally within it
- A module-closed _formula_ is a boolean-valued module-closed expression.
- A constant expression is a (module-complete) expression that (after expanding all definitions):
  - has no declared variables
  - has no non-constant operators.
    e.g. some non-constant operators are "'"(prime) and UNCHANGED
- The value of a constant expression depends only on the values of the declared constants it contains.
- An assumptionat (ASSUME) must be a constant formula.
- A state expression can contain anything a constant expression can as well as declared variables.
- The value of a state expression depends on:
  - The value of declared constants
  - The value of declared variables
- A state expression has a value on a state. A state assigns values to variables.
- A constant expression is a state expression that has the same value on all states.
- An action expression can contain anything a state expression can as well as "'"(prime) and UNCHANGED.
- A state expression has a value on a step (a step is a pair of states).
- A state expression is an action expression whose value on the step "s -> t" depends only on state _s_.
- An action formula is simply called an action.
- A temporal formula has a boolean value on a sequence of states (behavior)
- TLA+ has only boolean-valued temporal expressions.

- example spec
  initial formula     TPInit
  next-state formula  TPNext
TPSpec should be true on s1 -> s2 -> s3 -> ... iff
  TPInit is true on s1
  TPNext is true on s<sub>i</sub> -> s<sub>i+1</sub> for all `i`

TPInit is considered to be an action

- "⎕" typed "[]" in ASCII, is read as _always_. The 'always' operator.
- ⎕TPNext - "Always TPNext"
- TPSpec ≜ TPInit /\ [⎕TPNext]<<v1,v2,v3>>
  The specification with
    initial formula _Init_
    next-state formula _Next_
    declared variables _v1,...vn_
  is expressed by the temporal formula
  Init /\ ⎕[Next]<<v1...,vn>>
- For a temporal formula TF;
  `THEOREM TF`
  asserts that TF is true on every possible behavior
- THEOREM TPSpec => []TPTypeOK
  Asserts that for every behavior:
  - if TPSpec is true on the bheavior
    then []TPTypeOK is true on the behavior (means TPTypeOK is true on every state of the behavior)
  Asserts that TPTypeOK is an invariant of TPSpec

- INSTANCE TCCommit
  THEOREM TPSpec => TCSpec
    Asserts that for every behavior:
      if it satisfies TPSpec
      then it satisfies TCSpec

- specifications are not programs; they're mathematical formulas
- a specification does not describe the correct behavior of a system,
  rather it describes a universe in which the system and its environment are
  behaving correctly.
  The spec says nothing about irrelevant parts of the universe.

- THEOREM TPSpec => TCSpec
  This theorem makes sense because both formuals are assertions about the same
  kinds of behavior.
  It asserts that every behavior satisfying TPSpec satisfies TCSpec.

- Steps that leave all the spec's variables unchanged are called stuttering steps
- Every TLA+ spec allows stuttering steps
- We represent a terminating execution by a behavior ending in an infinite sequence
  of stuttering steps.
  The universe keeps going even if the system terminates.
  All behaviors are infinite sequences of states.
- Specs specify what the system _may_ do.
  They don't specify what it _must_ do.
  These are different kinds of requirments and should be specified seperately.

lession 9
- tuples are simply finite sequences
- << -3, "xyz", {0,2} >> is a sequence of length 3
- A sequence of length N is a function with domain 1..N
  - << -3, "xyz", {0,2} >>[1] = -3
  - << -3, "xyz", {0,2} >>[2] = "xyz"
  - << -3, "xyz", {0,2} >>[3] = {0,2}
- The sequence <<1,4,9,...,N^2) is the function such that
    <<1,4,9,...,N^2>>[i] = i^2
  for all i in 1..N
  This is writen as:
    [i \In 1..N |-> i^2]
- Tail(<<s1,..,sn>>) equals <<s2,...,sn>>
- Head(seq) == seq[1]
- "◦" (concatenation) written as "\o" concaneates two sequences
  <<3,2,1>> ◦ <<"a","b">> = <<3,2,1,"a","b">>
- any non-empty sequence is the concaneation of it's head with it's tail
  IF seq # <<>> THEN seq = <<Head(seq)>> \o Tail(seq)
- The Append operator appends an element to the end of the sequence
  Append(seq, e) == seq \o <<e>>
- The operator Len applied to a sequence equals the sequences' length
  Len(seq)
  The domain of a sequence `seq` is `1..Len(seq)`
  1..0 = {}, which is the domain of <<>>
- Seq(S) is the set of all sequences with elements in _S_.
  Seq({3}) = {<<>>, <<3>>, <<3,3>>, <<3,3,3>>, ...} (infinite sequences)

- Remove(i, seq) == [j \in 1..(Len(seq) - 1) |-> IF j < i THEN seq[j] ELSE seq[j + 1]]
- Len(Remove(i, seq)) = Len(seq) -1

more here: https://tla.msr-inria.inria.fr/tlatoolbox/doc/model/overview-page.html
Glossary
- TLC - TLA+ model checker
- TLA+ Toolbox - create specs and run tools on them
- TLAPS - the TLA+ proof system
- Deadlock - Execution stopped when it wasn't supposed to.
- Termination - Execution stopped when it was suppose to.
- The TLA+ syntax for an array valued expression:
  [ variable ∈ set ↦ expression ]
  example:
    sqr ≜ [i ∈ 1..42 ↦ i^2]
  defines _sqr_ to be an array with index set 1..42
  such that _sqr[i] = i^2 for all i in 1..42_
- "↦" is typed as "|->" in ASCII
- in Math, we use parentheses for function application instead of brackets
- in TLA+ we write formulas not programs so we use math terminology,
  function instead of array, domain instead of index set,
  however TLA+ uses square brackets for function application to avoid confusing with
  another way mathemiatics uses paranethesis
- Math and TLA+ allow a function to have any set as its domain, for example, the set of all integers
- The for all symbol "∀" is typed as "\A" in ASCII

Syntax
- _EXTENDS Integers_ - imports arithmetic operators like "+"and ".."
- _VARIABLES i, pc_ - Declares identifiers
_ "Init" and "Next" are convention names used
- <>[]P - a termporal operator that every behaviour must conform to where eventually P becomes true and then always stays true. P may switch between true or false but must be true when program terminates.

Operators
- /\ - "AND"
- \/ - "OR"
- ~ - "not" negation
- "->" - ("if-then") implication
-  ≡ or "⇔" <=>" (if-and-only-if) "equivalence"
- the exponentiation operator is represented by the carat chractor e.g. (i^2)

Terminology
|Programming|Math|
|array|function|
|index set|domain|
|f[e]|f(e)|
|||

pcal program.tla && tlc program.tla
tlatex program.tla
pdflatex program.tex

--
pron notes
part 1
- TLA+ is like a blueprint when designing a house
- In TLA+ the abstraction/implementation relation is expressed by logical implication: X ⇒ Y is the proposition that X implements Y, or conversely that Y abstracts X.
- specifying in TLA+ is ultimately specifying with mathematics. But math doesn't save you from thinking; it just helps you organize your thoughts
- a signature, which is a set of symbols with a specifiy _arity_ - how many arguments the symbol takes. Example "5 (0-ary)", "= (2-ary)", "< (2-ary)", "* (2-ary)"
- expressions can have _quantifier_, like \A ("for all") and "existential quantifier" "\E" ("there exists")
- "\A x ..." means "for all objects s such that ..."
- "\E x ..." means "there exists an object x such that ..."
- a well-formed expression is called a _term_ (of the language), so the syntax is thought of as the set of all the terms
- a _formula_ is a boolean-valued expression, either true or false
- Variables that appear in a formula unbound are called _free variables__
- A formula that has no free variables is called a _sentence_ or _closed formula_
- A _model_ is the relationship between the syntax and semantics: a model of a formula is a structure that _satisfies_ it.
- It satisfies it by assigment of values to the variables taht make the formula true (truth is a semantic property).
- "⊨" "|=" is the symbol for "satisfies", on the left is a structure that make the formula on the right true
- The collection of all models of a formula A forms its _formal semantics_ is written as "[[A]]"
- Examples
  - [[A∧B]]=[[A]]∩[[B]] - the model for "A /\ B" is the intersection of model A with model B
  - [A∨B]]=[[A]]∪[[B]] - the model for "A \/ B" is the union of model A with model B
  - [[¬A]]=[[A]]c - the model ~A is the complement of the model A
- when working with logic, we work within a specific _logical theory_, which is a set of formulas called _axioms_, taken to be equivalent to TRUE.
- a model of a theory is a structure that satisfies all axioms of the theory; the theory specifies a model.
- Peano axioms - logical theory that characterizes the natural numbers and familiar arithmetic operations
- A logic also hash a _calculus_ a syntactic system for deriving expressions from other expressions, like _natural deduction_.
  - If formula _C_ can be derived by a finite number of application of inference rules from formulas _A_ and _B_, we write _A,B ⊢ C_, and
      say that A and B _prove_ C or _entail_ C, where A and B are the assumptions.
  - If formula A is entaile dby theory's axioms alone without any other assumptions, we write ⊢A and say A is a _tautology_
  - If  ⊢A and A is not an axiom, we say that A is a _theorem_. If we want to prove the theorem A, but we havne't yet done so, we call A a _proposition_

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
