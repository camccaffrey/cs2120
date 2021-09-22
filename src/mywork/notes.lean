/- ?/?/2021

introduction rule - used to create proofs

elimination rule - use proofs as the sum of their inputs
-/



/- Friday 9/17

if and only if:
    P implies Q     and     Q implies P

inference rules for "true"
    introduction:   true.intro

no proofs of "false"
    otherwise it would be true?
-/



/- Monday 9/20

Given a proposition, P, we can form a new proposition, usually written as ¬P, which we pronounce as "not P," and which we define in such a way as to assert that P is not true.

If ¬P is true, than P has no proofs

So the way we're going to say ¬P is to say if P were true then something that is completely impossible would happen. Because the impossible cannot happen, threefore there must be no proof of P

What we're going to take as 'the impossible thing" is that there is a proof of false. Here, defined false means we have a proposition with no proofs (otherwise, it'd be true), so to have a proof of false is an impossibility. 
-/

-- does false imply false?
example: false → false :=
begin
    assume f,
    exact f
end

--does false imply true?
example: false → true :=
begin
    assume f,
    exact true.intro,
end 

--does true imply true?
example: true → true :=
begin
    assume t,
    exact true.intro,
end 

--does true imply true?
example: true → false :=
begin
    assume t,
end

/-
It is this analysis that leads to the definition of ¬P. For any proposition P, we define ¬P to be the proposition, P → false. What this means is that if there is a proof of P → false, then we can condlude (by definition) ¬P. This is the introduction rule for ¬.
-/
#check not  -- see definition in lean library

/-
Example. Prove 0 = 1
-/
example : false := -- not possible
begin
end

example : ¬ false := --means false implies false
begin
 assume f,
 exact f
end 

example : ¬ 0 = 1 :=
begin
    assume h,

end

/-
To understand how to finish off the proof aove, we need to talke about case analysis again. Remember that we've used it to reason from a proof of a disjunction. Suppose we wnat to know that P ∨ Q → R. We start by assuming that we have a proof, pq, or P ∨ Q, and then we need to show that R follows as a logical consequence.

But there are exactly two possuble forms that a proof of P ∨ Q can take (or.intro_left p) and (or.intro_right q), where p and q are proofs of P and of Q, respectively. What we therefore need to show is that no matter which of these two forms of proof we have of P ∨ Q, that the truth of R follows. So we do a case analysis of pq.

In the first case, we assume P ∨ Q is true because P is. In this case we need to show athat P → R. In the second case, wehere P ∨ Q is true because Q is, we need to show that Q → R.  
-/

example: ∀ (P Q R : Prop), P ∨ Q → R :=
begin
    assume P Q R,
    assume pq,
    cases pq, -- 2 subgoals
end

example: true → true :=
begin
    assume t,
    cases t, -- 1 subgoal
end

example: ¬ (0 = 1) :=
begin
    assume h,
    cases h,    --elimination rule for proof of false
end


theorem false_elim (P : Prop) (f: false) : P :=
begin
    exact false.elim f
end