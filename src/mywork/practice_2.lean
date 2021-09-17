/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.
-/

example : true := true.intro

example : false := _   -- trick question? why?
/-
This is a trick question because there is no proof of "false"
-/

example : ∀ (P : Prop), P ∨ P ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  -- forward direction
    assume porp,
    apply or.elim porp,
    -- left disjunct is true
      assume p1,
      exact p1,
    -- right disjunct is true
      assume p2,
      exact p2,
  -- backwards direction
    assume p,
    apply or.intro_left,
    exact p
end

example : ∀ (P : Prop), P ∧ P ↔ P := 
begin
  assume P,
  apply and.intro _ _,
end

example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
begin
end

example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
begin
end

example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
end

example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
end

example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
end

example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
end

example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
end

example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
end

example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
end

example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
end


