/-
Group: Earth, Wind, and Fire

Connor McCaffrey, cam7qp@virginia.edu, https://github.com/camccaffrey/cs2120.git
Jumi Hall, jah5py@virginia.edu, https://github.com/hubdaha/cs2120f21.git
Jakob Kauffmann, jgk2qq@virginia.edu, https://github.com/jakekauff/CS2120F21.git
-/

/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.
-/

example : true := true.intro

/-
true.intro is the introduction rule for "true" and returns a proof of true.
-/

example : false := _   -- trick question? why?
/-
This is a trick question because, by definition, there is no proof of "false."
-/

example : ∀ (P : Prop), P ∨ P ↔ P := 
/-
For arbitrary proposition P, we must show that P ∨ P if and only if P. To do this, we must show that P ∨ P → P and that P → P ∨ P
in order to use the introduction rule for "if and only if." For the first route, we assume P ∨ P and then apply the elimination rule for 
"or." We find proof of P in both cases. For the second route, we assume P and apply the introduction rule of "or" to prove that P ∨ P. 
QED.
-/
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
/-
For arbitrary proposition P, we must show that P ∧ P if and only if P. To do this, we must show that  P ∧ P → P and that P → P ∧ P in 
order to apply the introduction rule for "if and only if." For the first route, we asusme P ∧ P and apply the elimination rule of "and," 
reducing the expression to P → P. In the second route, we assume P and use the introduction rule for "and," filling both sides with P. 
Thus, we have proof that P → P ∧ P. QED.
-/
begin
  assume P,
  apply iff.intro _ _,
  --left
    assume pandp,
      apply and.elim pandp,
      assume p,
      assume p,
      exact p,
  --right
    assume p,
      apply and.intro p p,
end

example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
/-
For arbitrary propositions P and Q, we must show that P ∨ Q if and only if Q ∨ P. To do this, we must show that P ∨ Q → Q ∨ P and that
Q ∨ P → P ∨ Q to apply the introduction rule for "if and only if." For the first route, we assume P ∨ Q and use the elimination rule for 
"or" to explore two different cases. In the first case, we assume P and apply the introduction rule for "or" to the right side of Q ∨ P. 
In the second case, we assume Q and apply the introduction rule for "or" to the left side of Q ∨ P. This allows us to show that
P ∨ Q → Q ∨ P. For the seond route, we assume Q ∨ P and use the elimination rule for "or" to explore two differnt cases. In the first 
case, we assume Q and apply the introduction rule for "or" to the right side of P ∨ Q. In the second case, we assume P and apply the 
introducton rule for "or" to the left side of P ∨ Q. This allows us to show that Q ∨ P → P ∨ Q. QED.
-/
begin
  assume P Q,
  apply iff.intro _ _,
  --left
    assume porq,
      apply or.elim porq,
        assume p,
        apply or.intro_right;
        exact p,
      apply or.intro_left,
  --right
    assume qorp,
      apply or.elim qorp,
        assume Q,
        apply or.intro_right,
        exact Q,
      apply or.intro_left,
end

example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
/-
For arbitrary propositions P and Q, we must show that P ∧ Q if and only if Q ∧ P. To do this, we must show that P ∧ Q → Q ∧ P and that
Q ∧ P → P ∧ Q to apply the introduction rule for "if and only if." For the first route, we can use the elimination rule for "and" on the 
left and right side to prove both P and Q. Then, the introduction rule for "and" can be used on Q and P to prove Q ∧ P. For the second 
route, we can use the elimination rule for "and" on the left and right side to prove both Q and P. Then, the introduction rule for "and" 
can be used on P and Q to prove P ∧ Q. QED.
-/
begin
  assume P Q,
  apply iff.intro _ _,
  --left
    assume pandq,
      have p : P := and.elim_left pandq,
      have q : Q := and.elim_right pandq,
      have qp : Q ∧ P := and.intro q p,
      exact qp,
  --right
    assume qandp,
      have q : Q := and.elim_left qandp,
      have p : P := and.elim_right qandp,
      have pq : P ∧ Q := and.intro p q,
      exact pq,
end

example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
/-
For arbitrary propositions P Q R, we must show that P ∧ (Q ∨ R) if and only if (P ∧ Q) ∨ (P ∧ R). To do this, we must show that
P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R) and that (P ∧ Q) ∨ (P ∧ R) → P ∧ (Q ∨ R) to apply the introduction rule for "if and only if." For the 
first route, we assume P ∧ (Q ∨ R) and use the left and right elimination rules of "and" to prove P as well as Q ∨ R. Then, the 
elimination rule for "or" is applied to Q ∨ R, creating two cases to explore. In the first case, we assume Q and apply the introduction 
rule for "or" to (P ∧ Q) ∨ (P ∧ R) with the goal of prooving P ∧ Q. We can go about this by using the introduction rule for "and " with P 
and Q. In the second case, we assume R and apply the introduction rule for "or" to (P ∧ Q) ∨ (P ∧ R) with the goal of prooving P ∧ R. We 
can go about this by using the introduction rule for "and" with P and R. For the second route, we assume (P ∧ Q) ∨ (P and R) and use the 
elimination rule for "or" on both sides, creating two cases for exploration. In the first case, we assume P ∧ Q and apply the elimination 
rule for "and" to both sides to prove both P and Q. Then, we can use the introduction rule for "or" to Q ∨ R using our proof of Q. Now, 
we can use the introduction rule for "and" with P and (Q ∧ R) to prove P ∧ (Q ∨ R). IN the second case, we assume P ∧ R and apply the 
elimination rule for "and" to both sides to prove both P and R. Then, we can use the introduction rule for "or" to Q ∨ R using our proof 
of R. Now, we can use the introduction rule for "and" with P and (Q ∨ R) to prove P ∧ (Q ∨ R). QED.
-/
begin
  assume P Q R,
  apply iff.intro _ _,
  --left
    assume p_qorr,
    have p : P := and.elim_left p_qorr,
    have qorr : Q ∨ R := and.elim_right p_qorr,
      apply or.elim qorr,
      --left disjunct
        assume q,
        apply or.intro_left,
        apply and.intro p q,
      --right disjunct
        assume r,
        apply or.intro_right,
        apply and.intro p r,   
  --right
    assume pq_pr,
      apply or.elim pq_pr,

      assume pq,
        have p : P := and.elim_left pq,
        apply and.intro p _,
          apply or.intro_left,
          exact and.elim_right pq,

      assume pr,
        have p : P := and.elim_left pr,
        apply and.intro p _,
          apply or.intro_right,
          exact and.elim_right pr,

end

example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
/-
For arbitrary propositions P Q R, we must show that P ∨ (Q ∧ R) if and only if (P ∨ Q) ∧ (P ∨ R). To do this, we must show that
P ∨ (Q ∧ R) → (P ∨ Q) ∧ (P ∨ R) and that (P ∨ Q) ∧ (P ∨ R) → P ∨ (Q ∧ R) in order to apply the introduction rule for "if and only if." 
For the first route, we assume P ∨ (Q ∧ R) and apply the elimination rule for "or," creating two cases for exploration. In the first 
case, we assume P and apply the elimination rule for "and" on both sides of (P ∨ Q) ∧ (P ∨ R) to prove both P ∨ Q and P ∨ R. We can prove 
both of these propositions by applying the introduction rule for "or" to the left side of both statements with our proof of P. In the 
second case, we assume Q ∧ R and apply apply the elimination rule for "and" to prove both Q and R. We can also apply the elimination rule 
for "and" on both sides of (P ∨ Q) ∧ (P ∨ R) to prove both P ∨ Q and P ∨ R. We can then prove P ∨ Q by applying the introduction rule of 
"or" to the right side with our proof of Q, and we can prove P ∨ R by applying the introduction rule of "or" to the left side with our 
proof of R. For the second route, we assume (P ∨ Q) ∧ (P ∨ R) and apply the elimination rule for "and" to prove both P ∨ Q and P ∨ R. In 
the case where we assume P, we can prove  P ∨ (Q ∧ R) by applying the introduction rule for "or" to the left side with our proof of P. In 
the case where we assume both Q and R, we can use the introduction rule of "and" to show proof of Q ∧ R. We can then prove P ∨ (Q ∧ R) by 
applying the introduction rule of "or" to the right side with our proof of Q ∧ R. QED.
-/
begin
  assume P Q R,
  apply iff.intro _ _,
  --left
    assume p_qr,
      apply or.elim p_qr,
      --left
        assume p,
          apply and.intro _ _,
            apply or.intro_left,
              exact p,
            apply or.intro_left,
              exact p,
      --right
        assume qr,
          apply and.intro _ _,
            apply or.intro_right,
              apply and.elim_left qr,
            apply or.intro_right,
              apply and.elim_right qr,
  --right
    assume pqpr,
    have porq : P ∨ Q := and.elim_left pqpr,
    have porr : P ∨ R := and.elim_right pqpr,
    apply or.elim porq,
      assume p,
        apply or.intro_left,
        exact p,

      assume q,
    
    apply or.elim porr,
      assume p,
        apply or.intro_left,
        exact p,
      assume r,
      have qr: Q ∧ R := and.intro q r,
      apply or.intro_right,
      exact qr,

end

example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
/-
For arbitary propositions P Q, we must show that P ∧ (P ∨ Q) if and only if P. To do this, we must show that P ∧ (P ∨ Q) → P and that
P → P ∨ (P ∧ Q) in order to apply the introduction rule for "if and only if." For the first route, we assume P ∧ (P ∨ Q) and apply the 
elimination rule for "and" to the left to proove P. For the second route, we must be able to show that P ∨ Q so that we can apply the 
introduction rule for "and" using P and P ∨ Q. To prove P ∨ Q, we use the introduction rule for "or" on the left side with our assumed 
proof of P. QED.
-/
begin
  assume P Q,
  apply iff.intro _ _,
  --left
    assume ppq,
      exact and.elim_left ppq,
  --right
    assume p,
      apply and.intro p _,
        apply or.intro_left,
        exact p,

end

example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
/-
For arbitary propositions P Q, we must show that P ∨ (P ∧ Q) if and only if P. To do this, we must show that P ∨ (P ∧ Q) → P and that
P → P ∨ (P ∧ Q) in order to apply the introduction rule for "if and only if." For the first route, we assume P ∨ (P ∧ Q) and apply the 
elimination rule for "or," leaving us with two cases to explore. In the first case, we assume P and it follows that P → P. In the second 
case, we assume P ∧ Q and use the elimination rule for "and" on the left size to show proof of P. QED. For the second route, we assume P 
and prove P ∨ (P ∧ Q) by applying the introduction rule for "or" on the left side with our assumed proof of P. QED. 
-/
begin
  assume P Q,
  apply iff.intro _ _,
  --left
    assume p_pq,
    apply or.elim p_pq,
      assume p,
        exact p,
      assume pq,
        apply and.elim_left pq,
  --right
    assume p,
      apply or.intro_left,
      exact p,

end

example : ∀ (P : Prop), P ∨ true ↔ true := 
/-
For arbitrary proposition P, we must show that P ∨ true if and only if P. To do this, we must show that P ∨ false →P and that
P → P ∨ false in order to apply the introduction rule for "if and only if." For the first route, we assume P ∨ true and apply the 
elimination rule for "or," creating two cases for exploration. In the first case, we assume P and it follows that P → P. In the second 
case, we assume true and use the introduction rule for "true" as proof of true. For the second route, we assume P and prove P ∨ false by 
applyng the introduction rule for "or" to the left side with our assume proof of P. QED.
-/
begin
  assume P,
  apply iff.intro _ _,
  --left
    assume port,
    apply true.intro,
  --right
    assume t,
    apply or.intro_right,
    exact t
end

example : ∀ (P : Prop), P ∨ false ↔ P := 
/-
For arbitrary proposition P, we must show that P ∨ false if and only if P. To do this, we must show that P ∨ false → P and that
P → P ∨ false in order to apply the introduction rule for "if and only if." For the first route, we assume P ∨ false and apply the 
elimination rule for "or," creating two cases for exploration. In the first case, we assume P and it follows that P → P. In the second 
case, we assume false and use case analysis to show proof of P. For the second route, we assume P and prove P ∨ false by applying the 
introduction rule for "or" to the left side with our assumed proof of P. QED.
-/
begin
  assume P,
  apply iff.intro _ _,
  --left
    assume porf,
      apply or.elim porf,
      --left
        assume p,
        exact p,
      --right
        assume f,
        cases f,
  --right
    assume p,
      apply or.intro_left,
      exact p,
end

example : ∀ (P : Prop), P ∧ true ↔ P := 
/-
For arbitrary proposition P, we must show that P ∧ true if and only if P. To do this, we must show that P ∧ true → P and that
P → P ∧ true in order to apply the introduction rule for "if and only if." For the first route, we assume P ∧ true and apply the 
elimination rule for "and" to the left side to proove P. For the second route, we assume P and use the introdution rule for "true" as our 
proof of true. Then, we can apply the introduction rule for "and" using our proof of P and true to show that P ∧ true. QED.
-/
begin
  assume P,
  apply iff.intro _ _,
  --left
    assume pt,
    apply and.elim_left pt,
  --right
    assume p,
    apply and.intro p (true.intro)
end

example : ∀ (P : Prop), P ∧ false ↔ false := 
/-
For arbitrary proposition P, we must show that P ∧ false if and only if false. To do this, we must show that P ∧ false → false and that 
false → P ∧ false in order to apply the introduction rule for "if and only if." For the first route, we assume P ∧ false and apply the 
elimination rule for "and" to the right side to show that P ∧ false → false. For the second route, we assume false and must do case 
analysis before applying the introduction rule for "and" to show that false → P ∧ false 
-/
begin
  assume P,
  apply iff.intro _ _,
  --left
    assume pf,
    apply and.elim_right pf,
  --right
    assume f,
    apply and.intro _ f,
    cases f,
end


