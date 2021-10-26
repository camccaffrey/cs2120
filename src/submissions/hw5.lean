-- File: hw5.lean
-- Author: Connor McCaffrey (cam7qp)
-- Repository: https://github.com/camccaffrey/cs2120
-- Date: 10/25/2021

import data.set

/-
CS2120 F21 HW5

The goals of this assignment are to give you
practice with proofs of propositions that use
existential quantificaton, and to develop your
understanding of formal and informal proofs in
set theory.
-/

/-
PART I: EXISTENTIAL QUANTIFICATION.
-/

/-
To start, suppose that α and β are arbitrary
types, and p and q are predicates on values
of these types: α and β, respectively.
-/

axioms 
  (α β : Type)    -- data types
  (p : α → Prop)  -- predicates
  (q : β → Prop)

/-
In this context complete the following tasks:

(1) Write a fluent English-language statement
of the proposition to be proved. 

(2) Provide a formal proof of the proposition.

(3) Write an informal proof of the proposition.
-/

-- here's the proposition
example : 
  (∃ (f : α → β), ∀ (a : α), p a → q (f a)) →
  (∃ (a : α), p a) → 
  (∃ (b : β), q b) := 

/-
What does this propositon say? Explain it in
plain English. Here's a start: "If there's a 
function that maps/takes every α value that ... 

-- your completed English rendition here:

If (1) there exists a function "f" that implies a value
of type "β" from a value of type "α" for all "a" of
type "α", and if (2) a predicate "p" for "a" being true
implies that another predicate, q, for "f applied to a"
is also true, and if (3) there exists an "a" of type "α" 
for which "p applied to a" is true, then we know there
exists a "b" of type "β" for which predicate "q applied
to b" is true.
-/

-- Give your formal proof here
begin
  assume h1, -- h1: ∃ (f : α → β), ∀ (a : α), p a → q (f a)
  assume h2, -- h2: ∃ (a : α), p a ⊢ ∃ (b : β), q b

  apply exists.elim h1,
  apply exists.elim h2,

  assume alpha,           -- α
  assume p_applied_to_alpha,  -- p alpha
  assume alpha_imp_beta,  -- α → β
  assume pa_imp_qb,       -- ∀ (a : α), p a → q (alpha_imp_beta a)
                          --  ⊢ ∃ (b : β), q b

  apply exists.intro _ _,

  apply alpha_imp_beta alpha,
  apply pa_imp_qb alpha,
  apply p_applied_to_alpha,
  
end

-- Give your informal proof here

/-
First, we assume that (A) there exists a function "f" that
implies a value of type "β" from a value of type "α" for
all "a" of type "α", (B) a predicate "p" for "a" being true
implies that another predicate, q, for "f applied to a" is also
true, and (C) there exists an "a" of type "α" for which
"p applied to a" is true. Next, we can apply the elimination
rule of exists to these assumptions in order to assume the
following: (D) there exists an object "a" of type "α",
(E) proposition "p" applied to "a" is true, (F) an object of
type "α" implies an object of type "β", and (G) if for all "a"
of type "α", predicate "p" applied to "a" is true, and if that
implies that predicate "q" when applied to the predicate
"α → β applied to a" is also true, then there exists a "b" of
type "β" for which predicate "q" applied to "b" is true. We can
then apply the introduction rule of exists in order to reduce
our goal to act of proving an object of type "β". By applying
the predicate "an object of type α implies an object of type β"
to our instance of "α", we can again reduce our goal to proving
that predicate "q" applied to the aformentioned predicate is
true. We further reduce our goal to proving that predicate "p"
applied to "α" is true by appling assumption (G) to "α". Since
this was assumed to be true in assumption (E), simply apply the
assumption. QED
-/


  