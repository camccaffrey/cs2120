
/-
the foundation of any logic is a set of inference rules. There are many logics. Each logic is characterized by its inference rules. In predicate logic, we have an and connective; it has an inference rule that allows you to prove the proposition P ∧ Q. On top of the inference rules, we derive theorems, which become just as good as the inference rules. For example, "and commonicative: for any propositions P and Q, if P and Q ix true, then Q and P is true" is a theorem derived by inference rules (introduction, elimination) of and. As long as the logic is consistent, you won't arrive at contradictions
-/

-- 1
example : 0 ≠ 1 :=
/-
inference rules: equality and negation

assumptions lead to a contradiction

assume 0 = 1
show that false is true in that context
case analysis on h: false is true in all 0 cases
could use "trivial"
-/
begin
  -- ¬ (0 = 1)
  -- (0 = 1) → false
  assume h,
  cases h,
end


-- 2
example : 0 ≠ 0 → 2 = 3 :=
/-
same as above?

eq.refl 0 - some proofs are not explicitly stated in the question


-/
begin
  assume h,
  have f : false := h (eq.refl 0),
  exact false.elim (f),
end

-- 3
example : ∀ (P : Prop), P → ¬¬P :=
/-
introduce double negation constructively

the converse of the implication aboce is not true (without classical)

assume P

not means "implies false"


-/
begin
  assume P,
  assume (p : P),
  -- ¬¬P
  -- ¬P → false
  -- (P → false) → false
  assume h,
  have f := h p,
  exact f,
end 

-- We might need classical (vs constructive) reasoning 
#check classical.em
open classical
#check em

/-
axiom em : ∀ (p : Prop), p ∨ ¬p

This is the famous and historically controversial
"law" (now axiom) of the excluded middle. It's is
a key to proving many intuitive theorems in logic
and mathematics. But it also leads to giving up on
having evidence *why* something is either true or
not true, in that you no longer need a proof of 
either P or of ¬P to have a proof of P ∨ ¬P.
-/

-- 4
theorem neg_elim : ∀ (P : Prop), ¬¬P → P :=
/-
converse of the last theorem

proof by contradiction

to prove p by contradiction, assume not p and show contradiction. then assume not not p




proof by negation: prove not p
  assume p
  show false
  show that p implies false
  (literal definition of not p)

proof by contradiction: prove p
  assume not p
  show this leads to a contradiction
  this prooves not not p


h really means p implies false implies false, no obvious way to get proof of p

only have stand alone proposition to work with -> case analaysis on disjunction
  law of excluded middle - classical.em universal generalization

  apply axiom to get a proof of p or not p

  case analysis
    left: p and P
    right not p and not not p - contradiction



-/
begin
  assume P,
  assume h,
  have pornp := classical.em P,
  cases pornp with p pn,
  assumption,
  contradiction,
end

-- 5
theorem demorgan_1 : ∀ (P Q : Prop), ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
/-
demorgan laws
  given propositions p and q, if p and q is false, then at least one of p or q have to be false

  conversely, if one of them is false, there is no way that the conjunction is true


assume propositions p and q
apply iff.intro, returns two subgoals (top down reasoning)
  shortcut: use "split"

--foward
  assume hypothesis of implication
  law of the excluded middle to both p and q
  case analysis
    cases (classical.em P) with p np - label proof of p and not p
    cases (classical.em Q) with q nq

  show that proposition is true in all four cases
    1. contradiction between p and q  and  -p and q
      contradiction
    2 ...
    3. or.intro on not p
    4. or.intro on not p

--backwards
  "admit" - accept random axiom of true --not necessary
  he says never to use this, not sure why he brought it up

  didnt explain this part

-/
begin
end


-- 6
theorem demorgan_2 : ∀ (P Q : Prop), ¬ (P ∨ Q) → ¬P ∧ ¬Q :=
/-
demorgan 2 - a distributive law
 if p or q is not true, then both p and q are not true


assume p and q
asssume h
cases (classical.em P) with p np,
cases (classical.em Q) with q nq,

have porq := or.intro_left Q p, <- have to use this specific syntax for some reason
conradiction

have porq := or.intro_left Q p, <- have to use this specific syntax for some reason
conradiction

cases (classical.em Q) with q nq
  build a proof of p or q with p and then show contradiction
  ...



-/
begin
end


-- 7
theorem disappearing_opposite : 
  ∀ (P Q : Prop), P ∨ ¬P ∧ Q ↔ P ∨ Q := 
begin
end


-- 8
theorem distrib_and_or : 
  ∀ (P Q R: Prop), (P ∨ Q) ∧ (P ∨ R) ↔
                    P ∨ (Q ∧ R) :=
begin
end

-- remember or is right associative
-- you need this to know what the lefts and rights are
-- 9
theorem distrib_and_or_foil : 
  ∀ (P Q R S : Prop),
  (P ∨ Q) ∧ (R ∨ S) ↔
  (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S) :=
begin
end


/- 10
Formally state and prove the proposition that
not every natural number is equal to zero.
-/
lemma not_all_nats_are_zero : _ :=
begin
end 

-- 11. equivalence of P→Q and (¬P∨Q)
example : ∀ (P Q : Prop), (P → Q) ↔ (¬P ∨ Q) :=
begin
end

-- 12
example : ∀ (P Q : Prop), (P → Q) → (¬ Q → ¬ P) :=
begin
end

-- 13
example : ∀ (P Q : Prop), ( ¬P → ¬Q) → (Q → P) :=
begin
end

