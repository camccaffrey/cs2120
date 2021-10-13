/- 
   *******************************
   PART 1 of 2: AXIOMS [50 points]
   *******************************
-/

/-
Explain the inference (introduction and
elimination) rules of predicate logic as
directed below. To give you guidance on
how to answer these questions we include
answers for some questions.
-/


-- -------------------------------------

/- #1: → implies [5 points]

INTRODUCTION

Explain the introduction rule for →. 

[We give you the answer here.]

In English: Given propositions, P and Q, 
a derivation (computation) a proof of Q 
from any proof of P, is a proof of P → Q.

In constructive logic, a derivation is a
given as a function definition. A proof
of P → Q literally is a function, that,
when given any proof of P as an argument
returns a proof of Q. If you define such
a function, you have proved P → Q.

ELIMINATION

Complete the definition of the elimination
rule for →.

(P Q : Prop) (p2q : P → Q) (p : P)
---------------------------------- elim
               q : Q
-/

-- Give a formal proof of the following
example : ∀ (P Q : Prop) (p2q : P → Q) (p : P), Q :=
begin
  assume P,
  assume Q,
  assume p2q,
  exact p2q,
end

-- Extra credit [2 points]. Who invented this principle?

  -- Theophrastus of Ancient Greece

-- -------------------------------------


/- #2: true [5 points]

INTRODUCTION

Give the introduction rule for true using
inference rule notation.

[Here's our answer.]

---------- intro
(pf: true)

Give a brief English language explanation of
the introduction rule for true.

-- the proposition true is unconditionally true, 
  so the introduction rule of true always returns true.

ELIMINATION

Give an English language description of the
eliimination rule for true.

[Our answer]

A proof of true carries no information so
there's no use for an elimination rule.
-/

-- Give a formal proof of the following:

example : true := true.intro


-- -------------------------------------

/- #3: ∧ - and [10 points]

INTRODUCTION

Using inference rule notation, give the 
introduction rule for ∧.

[Our answer]

(P Q : Prop) (p : P) (q : Q)
---------------------------- intro
        (pq : P ∧ Q)

Given an English language description of
this inference rule. What does it really
say, in plain simple English. 

-- Given proof of proposition P and proof of proposition Q,
   then there is aslo proof of conjunction P ∧ Q through the
   introduction rule for and.

ELIMINATION

Given the elimination rules for ∧ in both
inference rule and English language forms.

(P Q : Prop) (pq : P ∧ Q)
----------------------------  left elim
        (p : P)

(P Q : Prop) (pq : P ∧ Q)
----------------------------  right elim
        (q : Q)

Left Elimination: Given propositions P and Q, if their conjunction P ∧ Q is true,
then proposition P is also true.

Right Elimination: Given propositions P and Q, if their conjunction P ∧ Q is true,
then proposition Q is also true.
-/



/-
Formally state and prove the theorem that, 
for any propositions P and Q,  Q ∧ P → P. 
-/

example : ∀ (P Q : Prop), Q ∧ P → P:=
begin
  assume p,
  assume q,
  assume pq,
  apply and.elim_right pq,
end


-- -------------------------------------

/- #4: ∀ - for all [10 points]

INTRODUCTION

Explain in English the introduction rule for ∀. If 
T is any type (such as nat) and Q is any proposition 
(often in the form of a predicate on values of the
given type), how do you prove ∀ (t : T), Q? What is
the introduction rule for ∀?

-- For any arbitrary t, if t satisfies property T, 
    then the property is true for all t. Because Q has
    values of this given type, they too satisfy the property.
    Thus, you have proof of Q.

ELIMINATION

Here's an inference rule representation of the elim
rule for ∀. First, complete the inference rule by
filling in the bottom half, then Explain in English
what it says.

(T : Type) (Q : Prop), (pf : ∀ (t : T), Q) (t : T)
-------------------------------------------------- elim
                (q : Q)


-- English language answer here

Given a proof, (pf : ∀ (t : T), Q), and a value, (t : T),
briefly explain in English how you *use* pf to derive a
proof of Q.

-- "pf" says that for any arbitrary t of type T, we have proof of Q.
    We can apply this thorem (like a function) to object t (because t
    is of type T) to ouput a proof of Q.

-/

/-
Consider the following assumptions, and then in the
context of these assumptions, given answers to the
challenge problems.
-/

axioms
  (Person : Type)
  (KnowsLogic BetterComputerScientist : Person → Prop)
  (LogicMakesYouBetterAtCS: 
    ∀ (p : Person), KnowsLogic p → BetterComputerScientist p)
  -- formalizee the following assumptions here
  -- (1) Lynn is a person
  -- (2) Lynn knows logic
  -- (3) if a perosn knows logic, then that person is a better computer scientist
  -- (4) Lynn is a better computer scientist

/-
Now, formally state and prove the proposition that
Lynn is a better computer scientist
-/
example : ∀ (Lynn : Person), KnowsLogic Lynn → BetterComputerScientist Lynn :=
begin
  assume Lynn,
  apply LogicMakesYouBetterAtCS Lynn
end



-- -------------------------------------

/- #5: ¬ - not [10 points] 

The ¬ connective in Lean is short for *not*. Give
the short formal definition of ¬ in Lean. Note that
surround the place where you give your answer with
a namespace. This is just to avoid conflicting with
Lean's definition of not.
-/

namespace hidden
def not (P : Prop) := P → false -- fill in the placeholder
end hidden

/-
Explain precisely in English the "proof strategy"
of "proof by negation." Explain how one uses this
strategy to prove a proposition, ¬P. 
-/

-- To prove ¬ P, you first assume P is true.
-- Then, you show that, in this context, assuming P leads to a contradiction.
-- This shows that P → false


/-
Explain precisely in English the "proof strategy"
of "proof by contradiction." Explain how one uses
this strategy to prove a proposition, P (notice 
the lack of a ¬ in front of the P). 

Fill in the blanks the following partial answer:

To prove P, assume "¬ P" and show that "this leads to a contradiction".
From this derivation you can conclude "¬ ¬ P".
Then you apply the rule of negation "elimination"
to that result to arrive a a proof of P. We have
seen that the inference rule you apply in the 
last step is not constructively valid but that it
is "classically" valid, and that accepting the axiom
of the "excluded middle" suffices to establish negation
"elimination" (better called double "negation" "elimination")
as a theorem.
-/



-- -------------------------------------

/- 
#6: ↔ - if and only if, equivalent to [10 points]
-/

/-
ELIMINATION 

As with ∧, ↔ has two elimination rules. You can 
see their statements here.
-/
#check @iff.elim_left
#check @iff.elim_right

/-
Formally state and prove the theorem that 
biimplication, ↔, is *commutative*. Note: 
put parentheses around each ↔ proposition,
as → has higher precedence than ↔. Recall
that iff has both elim_left and elim_right
rules, just like ∧.
-/

example : ∀ (P Q : Prop), (P ↔ Q) → (Q ↔ P):=
begin
  assume P,
  assume Q,

  apply iff.elim,

  --left
  assume p_imp_q,
  --right
  assume q_imp_p,

  have p_iff_q : Q ↔ P := iff.intro q_imp_p p_imp_q,
  apply p_iff_q,

end


/- 
   ************************************************
   PART 2 of 3: PROPOSITIONS AND PROOFS [50 points]
   ************************************************
-/

/- #7 [20 points]

First, give a fluent English rendition of
the following proposition. Note that the
identifier we use, elantp, is short for
"everyone likes a nice, talented person."
Then give a formal proof. Hint: try the
"intros" tactic by itself where you'd
previously have used assume followed by
a list of identifiers. Think about what
each expression means. 
-/

def ELJL : Prop := 
  ∀ (Person : Type) -- for all person : type
    (Nice : Person → Prop) -- takes Person and gives proposition Nice
    (Talented : Person → Prop) -- takes Person and gives propositon LIkes
    (Likes : Person → Person → Prop) -- takes two people and gives propostion Likes
    (elantp : ∀ (p : Person), Nice p → Talented p → ∀ (q : Person), Likes q p)
    (JohnLennon : Person)
    (JLNT : Nice JohnLennon ∧ Talented JohnLennon),
    (∀ (p : Person), Likes p JohnLennon) 
    
/-
English Rendition:
  For any arbitrary person Q, if person P is Nice and person P is Talented, then person Q Likes person P. Therefore, if John Lennon is a person, and John Lennon is Nice and John Lennon is Talented, then any arbitray person Q Likes John lennon. In other words, everyone likes John Lennon.

-/
example : ELJL :=
begin
  assume person_p,
  assume nice,
  assume talented,
  assume likes,
  assume elantp,
  assume JL,
  assume nice_and_talented, -- john lennon is person
  assume person_q,
  
  have niceJL : nice JL := and.elim_left nice_and_talented,
  have talentedJL : talented JL := and.elim_right nice_and_talented,
  
  apply elantp JL niceJL talentedJL,
end



/- #8 [10 points]

If every car is either heavy or light, and red or 
blue, and we want a prove by cases that every car 
is rad, then: 

-- how many cases will need to be considered? 4
-- list the cases (informaly)
    -- Car is Heavy and Red
    -- Car is Heavy and Blue
    -- Car is Light and Red
    -- Car is Light and Blue

-/

/-
  *********
  RELATIONS
  *********
-/


/- #9 [20 points]
Equality can be understood as a binary relation
on objects of a given type. There is a binary 
equality relation on natural numbers, rational 
numbers, on strings, on Booleans, and so forth.

We also saw that from the two axioms (inference
rules) for equality, we could prove that it is
not only reflexive, but also both symmetric and
transitive.

Complete the following definitions to express
the propositions that equality is respectively
symmetric and transitive. (Don't worry about
proving these propositions. We just want you
to write them formally, to show that you what
the terms means.)
-/

def eq_is_symmetric : Prop :=
  ∀ (T : Type) (x y : T), x = y → y = x

def eq_is_transitive : Prop :=
  ∀ (T : Type) (x y z : T), x = y → y = z → x = z


/-
  ************
  EXTRA CREDIT
  ************
-/

/- 
EXTRA CREDIT: State and prove the proposition
that (double) negation elimination is equivalent
to excluded middle. You get 1 point for writing
the correct proposition, 2 points for proving it
in one direction and five points for proving it
both directions. 
-/


def negelim_equiv_exmid : ∀ (P : Prop), (¬¬P → P) ↔ (¬ P → P ∨ ¬ P):= 
begin

end


/- 
EXTRA CREDIT: Formally express and prove the
proposition that if there is someone everyone
loves, and loves is a symmetric relation, then 
thre is someone who loves everyone. [5 points]
-/

axiom Loves : Person → Person → Prop

example : ∀ (p q : Person), Loves p q :=
begin
  
end
