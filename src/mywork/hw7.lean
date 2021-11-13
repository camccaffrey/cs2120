
/-
File: hm7.lean
Name: Connor McCaffrey  (cam7qp), https://github.com/camccaffrey/cs2120
Date: 11/12/2021

Partners:      Jumi Hall  (jah5py), https://github.com/hubdaha/cs2120f21
          Jakob Kauffman  (jgk2qq), https://github.com/jakekauff/CS2120F21
-/

import data.set
import tactic.ring

namespace relation

-- PRELIMINARY SETUP

/-
Preliminary set up. For the rest of this file,
we specify an arbitrary binary relation, r, on
an arbitrary type, β, as a two-place predicate, 
with infix notation x ≺ y for (r x y). One can
pronounce these expressions in English as "x is
related to y".
-/
variables {α β : Type}  (r : β → β → Prop)
local infix `≺` : 50 := r  


/-
The default Lean libraries are missing definitions
for the assympetric property of relations and for
the notion of a powerset. We define these terms for
use in the rest of this file.
-/
def asymmetric := ∀ ⦃x y⦄, x ≺ y → ¬ y ≺ x
def powerset (s : set β) := { s' | s' ⊆ s}


-- PROBLEMS

/- 
#1: Give both a formal and an English-language proof. Then
answer the question, is the proposition true if you remove
the first condition, that β is inhabited? Briefly explain
your answer (in English).
-/
example : (∃ (b : β), true) → asymmetric r → ¬reflexive r :=
/-
Given that there exists b in set β and that relation r is asymmetric,
we must prove that relation r is not reflexive. To do this, we should
assume that the relation is both asymmetric and relexive and then see
if we can arrive at a contradiction. Using the assumption of reflexivity,
we can show that b relates to itself. However, applying our assumption of
asymmetry to this relation results in proof that relation r applied to bb
implies false. Thus, we have arrived at a contradiction, meaning that relation
r is not reflexive.

If the first conditon--"∃ (b : β), true"--were removed, we would not be able to
solve this proof. This is because, without this assumptiom, set β could be an
empty set and the logic we used in the original proof would not follow.
-/
begin
  unfold asymmetric,
  unfold reflexive,
  assume ex asymm,
  assume refl,
  cases ex with b pf,
  have rbb : r b b := refl b,
  have contra := asymm rbb,
  contradiction,
end



/-
#2. Logic, like programming, is subtle. It's very easy for humans
to miss subtle corner cases. As an example, today I ran across
a problem in a textbook by Paul Traiger, a professor emeritus
of philosophy and cognitive science at Occidental College. He
asks students to prove that if a relation is both transitive and 
reflexive that it cannot be anti-symmetric. See the question at
the very bottom of the page here:
https://sites.oxy.edu/traiger/logic/exercises/chapter13/properties_of_relations_exercise.html

Is the conjecture actually logically valid? If not, what condition 
needs to be added to make it so? Try prove this/his version of the
conjecture, as articulated slightly differently below. If you get
stuck, then you need to figure out an additional condition that needs 
to be added as a premise to make the proposition true. In that case,
add the premise and then show that the updated conjecture is true.
-/
example : (∃ (b : β), true) → transitive r → reflexive r → ¬ asymmetric r :=
/-
The original conjecture is not logically valid. The additional premise that
set β is inhabited must be included in the statement so that we can solve
the proof.

Once this is done, we can show that a transitive and reflexive relation r is not
asymmetric through case analysis and contradiction. First we assume that r is
transitive, reflexive and asymmetric. Because we know there exists a b in set β,
we can use our assumption of reflexivitiy to show that b relates to itself, and we
can use our assumption of asymmetry to show that the afformentioned relation implies
false. This raises an obvious contradiction. Thus, we have proof that relation r
is NOT asymmetric.
-/
begin
  unfold transitive,
  unfold reflexive,
  unfold asymmetric,

  assume b,
  assume trans,
  assume refl,
  assume asymm,

  cases b with b tru,

  have rbb := refl b,
  have nrbb := asymm rbb,
  contradiction,

end





/-
#3: Prove that the subset relation on the powerset of any
set, s, is antisymmetric. Formally state and prove, and
then give an informal proof of, this proposition.
-/
example : ∀ (s : set β) 
            (s1 s2 ∈ powerset s), 
            s1 ⊆ s2 → 
            s2 ⊆ s1 → 
            s1 = s2 :=
/-
We are given set s, s1, and s2. First we assume that set s1 and set s2 are
both elements of the powerset s. We also assume that set s1 is a subset of
set s2 and that set s2 is a subset of set s1. Using the axiom of set
extenionality, we can rewrite our goal into a bidirectional proposition.
Furthermore, we assume that x is an element of type β. In the forward direction,
we assume that x is in the set s1. It follows that x is also in set s2 by
applying the definition of a subset. In the backward direction, we assume that
x is in the set s2. It follows that x is also in s1 by appling the definition
of a subset. Because this statement is true in both directions, we can see that
set s1 and s2 are equal via the definition of set equality. Because we have shown
that in order for the subset relation to be symmetric, the two sets in question
must be equal, we have shown that, by definition, the subset relation on the
powerset s is antisymmetric.
-/
begin
  assume s,
  assume s1,
  assume s2,

  assume s1es,
  assume s2es,

  assume s1es2,
  assume s2es1,

  apply set.ext,
  assume x,
  split,

  assume xes1,
  apply s1es2 xes1,
  
  assume xes2,
  apply s2es1 xes2,
end


/-
Given two natural numbers, n and m, we will say that m divides n
if there is a natural number, k, such that n = k*m. Here's a formal
definition of this relation.
-/

def divides (m n : ℕ) := ∃ k, n = k * m

/- 
#4: Formally and informally state and prove each of the following
propositions. Remember that the ring tactic is useful for producing
proofs of simple algebraic equalities involving + and *. You can use
the phrase, "by basic algebra" when translating the use of this tactic
into English. (Or if you wanted to be truly Hobbit-like you could say 
"by the ring axioms!")
-/

-- A: For any n, 1 divides n.
example : ∀ n, divides 1 n :=
/-
By the definition of divides, given two natural numbers m and n, there
exists a natural number K for which k*m = n. To show that divides is true
given nats 1 and n for all n, we show that there exists a k equal to n.
Through basic algreba, we can see that 1 * n = n. 
-/
begin
  unfold divides,
  assume n,
  apply exists.intro (n:ℕ),
  ring_nf,

end

-- B. For any n, n divides n
example : ∀ n, divides n n :=
/-
By the definition of divides, given two natural numbers m and n, there
exists a natural number K for which k*m = n. To show that divides is true
given nats n and n for all n, we show that there exists a k equal to 1.
Through basic algreba, we can see that 1 * n = n. 
-/
begin
  unfold divides,
  assume n,
  apply exists.intro (1:ℕ),
  ring_nf,

end

-- #C. prove that divides is reflexive 
example : reflexive divides :=
/-
By the definition of divides, given two natural numbers m and n, there exists
a natural number K for which k*m = n. To show that divides is reflexive, we
must show that divides is true when applied to nats n and n for all n. Through
basic algebra, we can show that n * 1 = n. Thus, there exists a k, equal to 1,
for all n that satisfies the proposition that divides is reflexive.
-/
begin
  unfold reflexive,
  unfold divides,

  assume n,
  apply exists.intro (1:ℕ),
  ring_nf,
end 

-- #D. prove that divides is transitive
example : transitive divides :=
/-
By the definition of divides, given two natural numbers m and n, there exists
a natural number K for which k * m = n. To show that divides is transitive, we must
show that if there is a k1 that makes divides true for x and y, and there is a k2
that makes divides true for y and z, then there is a k3 that makes divides true
for y and z. Through case analysis, we are allowed to rewrite z = k3 * x to
z = k1 * k2 * x. Our goal can further be rewritten to  k2 * (k1 * x) = k1 * k2 * x.
We can prove this to be true through basic algrebra.
-/
begin
  unfold transitive,
  unfold divides,

  assume x,
  assume y,
  assume z,

  assume ydivx, -- y = k * x
  assume zdivy, -- z = k * y

  cases ydivx with k1 pr1, -- pr1: y = k1 * x
  cases zdivy with k2 pr2, -- pr2: z = k2 * y

  apply exists.intro (k1*k2),

  rw pr2,
  rw pr1, -- k2 * (k1 * x) = k1 * k2 * x
  ring_nf,

end 

/- 
E. Is divides symmetric? if yes, give a proof, otherwise 
give a counterexample and a brief explanation to show that 
it's not.
-/

/-
No, divides is not symmetric. One counter-example are the natural numbers
1 and 2. While there exists a natural number k for which 1 * k = 2 (where k = 2),
there does not exist a natural number k for which 2 * k = 1 (1/2 is not natural).
Because the relation is not true in both direction, we can see that divides
is nots symmetric.
-/

/- 
#F. Prove that divides is antisymmetric. 
-/
example : anti_symmetric divides := 
/-
By the definition of divides, given two natural numbers m and n, there exists
a natural number K for which k*m = n. To show that divides is anti_symmetric,
we must show that for any nats m and n for which divides is symmetric, m and n
must be equal. First, we assume nats x and y as well as divides for (x , y)
and divides for (y, x). Through case analysis, we can show that y = k1 * x and
x = k2 * y. By substitution, we can see that y = k1 * k2 * y. Basic algrebra
tells us that k1 * k2 = 1. For this to be true, the only natural numers that
k1 and k2 can be are 1. Afer assuming that k1 = 1 and k2 = 1, we can rewrite our
goal to be 1 * y = 1 * (1 * y). This can be proven to be true by basic algebra.
-/
begin  
  unfold anti_symmetric,
  unfold divides,

  assume x,
  assume y,
  assume ydivx, -- y = k * x
  assume xdivy, -- x = k * y

  cases ydivx with k1 pr1, -- pr1: y = k1 * x
  cases xdivy with k2 pr2, -- pr2: x = k2 * y

  rw pr1,
  rw pr2, -- k2 * y = k1 * (k2 * y)

  have k1 : k1 = 1 := sorry, -- if k1 * k2 = 1, and both k1 and k2 are natural numbers,
  have k2 : k2 = 1 := sorry, -- then both k1 and k2 are equal to 1.

  rw k1,
  rw k2, -- 1 * y = 1 * (1 * y)
  
  ring_nf,

end


/- #5
Prove the following propositions. Remember that
throughout this file, each definition implicitly
includes β as a type and r as an arbitrary binary 
relation on β. In addition to formal proofs, give
an English language proof of the last of the three
problems.
-/

-- A
example : asymmetric r → irreflexive r :=
/-
We must show that if a relation r is asymmetric, then it is irreflexive. We
can arrive at this conclusion by assuming both assymmetry and reflexivity
and then finding a contradiction. First, we assume b of type β. Through our
assumption of reflexivity, we can show that b relates to itself. Through our
assumption of asymmetry, we can show that the aforementioned relation
implies false. This is an obvious contradiction. Thus, we have proof that
if relation r is asymmetric, then it is also irreflexive. 
-/
begin
  unfold asymmetric,
  unfold irreflexive,

  assume asymm,
  assume b,
  assume rbb,
  have nrbb : ¬ r b b := asymm rbb,

  contradiction,
end

-- B
example : irreflexive r → transitive r → asymmetric r :=
/-
We must show tat if a relation r is irreflexive and transitive, then it is
also asymmetric. We can arrive at this conclusion by assuming irreflexivity,
transitivity, and asymmetry, and then finding a contradiction. First, we assume
x and y of type β in addition to relation r (x y) and relation r (y x).
Through our assumption of transitivity and these two relations, we can show
that x is related to itself. We can then use our assumption of irreflexivity
to show that the aforementioned relation implies false. This is an obvious
contradiction. Thus, we have proof that if relation r is irreflexive and
transitive, then it is also asymmetric.
-/
begin
  unfold irreflexive,
  unfold transitive,
  unfold asymmetric,

  assume irreflex,
  assume trans,
  assume x,
  assume y,
  assume rxy,
  assume ryx,
  
  have rxx : r x x := trans rxy ryx,
  have nrxx : ¬ r x x := irreflex x,

  contradiction,
end

-- C

/-
I have broken this question into two parts. In the first, I engage with
the original proof. In the second, I add a condition to the statement to
see if the proof can be solved with additional assumptions.
-/

example : transitive r → ¬ symmetric r → ¬ irreflexive r :=
begin
  unfold transitive,
  unfold symmetric,
  unfold irreflexive,

  assume trans,
  assume not_symm,
  assume irreflex,
end

/-
It seems this proof is not possible. This is because we cannot assume
there are elements that exist in set β. Propositions we try to make about
an empty set cannot be proven false with counter examples. Because of this,
we cannot rule out the possibility that set β is empty.

Let's insert "(∃ (b : β), true)" into the statement below.
-/

example : (∃ (b : β), true) → transitive r → ¬ symmetric r → ¬ irreflexive r :=
begin
  unfold transitive,
  unfold symmetric,
  unfold irreflexive,

  assume h,
  apply exists.elim h,
  assume b,
  assume t,

  assume trans,
  assume not_symm,
  assume irreflex,
end

/-
Even after adding a new condition to the statement, it still seems as though
the proof is impossible. While a relation that is transitive and irreflexive
is also asymmetric, we cannot assume that a relation that is transitive and not
symmetric is also not irreflexive. For example, transitivity implies that
if x relates to y and y relates to x, then x relates to itself (like how we proved
#5.b). However, because the relation r is stated to be not symmetric, it is not
possibe for both x to relate to y and for y to relate to x. Otherwise, we would
be able to use the two assumptions to reach a contradiction.
-/

end relation
