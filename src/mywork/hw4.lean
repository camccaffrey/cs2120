/-
Group: Earth, Wind, and Fire

Connor McCaffrey, cam7qp@virginia.edu, https://github.com/camccaffrey/cs2120.git
Jumi Hall, jah5py@virginia.edu, https://github.com/hubdaha/cs2120f21.git
Jakob Kauffmann, jgk2qq@virginia.edu, https://github.com/jakekauff/CS2120F21.git
-/

-- 1
example : 0 ≠ 1 :=
begin
  -- ¬ (0 = 1)
  -- (0 = 1) → false
  assume h,
  cases h,
end


-- 2
example : 0 ≠ 0 → 2 = 3 :=
begin
  assume h,
  have f : false := h (eq.refl 0),
  exact false.elim (f),
end

-- 3
example : ∀ (P : Prop), P → ¬¬P :=
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
begin
  assume P,
  assume h,

  -- law of the excluded middle
  have pornp := classical.em P,

  cases pornp with p pn,
  assumption,
  contradiction,
end

-- 5
theorem demorgan_1 : ∀ (P Q : Prop), ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  assume P Q,
  apply iff.intro _ _,
  --left
    assume npq : ¬ (P ∧ Q),

    -- law of the excluded middle
    have pornp : P ∨ ¬P := classical.em P,
    have qornq : Q ∨ ¬Q := classical.em Q,

    cases pornp,
    cases qornq,

    have pq : P ∧ Q := and.intro (pornp) (qornq),
    have f : false := npq pq,

    exact false.elim f,
    apply or.intro_right,
    exact qornq,
    apply or.intro_left,
    exact pornp,

  -- right
  assume npornq,
    apply not.intro,
    cases npornq,
    assume pq,
    
    have p : P := and.elim_left pq,
    apply npornq p,
    assume pq,

    have q : Q := and.elim_right pq,
    apply npornq q,

end


-- 6
theorem demorgan_2 : ∀ (P Q : Prop), ¬ (P ∨ Q) → ¬P ∧ ¬Q :=
begin
  assume P Q,
  assume notpq : ¬(P ∨ Q),

  -- law of the excluded middle
  have pornp : P ∨ ¬P := classical.em P,
  have qornq : Q ∨ ¬Q := classical.em Q,
  cases pornp,
    have f : false := notpq (or.inl pornp),
    exact false.elim f,

  cases qornq,
    have f : false := notpq (or.inr qornq),
    exact false.elim f,
  
  apply and.intro pornp qornq,

end


-- 7
theorem disappearing_opposite : 
  ∀ (P Q : Prop), P ∨ ¬P ∧ Q ↔ P ∨ Q := 
begin
  assume P Q,
  apply iff.intro _ _,
  --left
    assume p_or_npandq,
    apply or.elim p_or_npandq,
      assume p,
      apply or.intro_left,
      exact p,
        assume npandq,
        have q:= and.elim_right npandq,
        apply or.intro_right,
        exact q,

  --right
    assume porq,
      apply or.elim porq,
      assume p,

    apply or.intro_left,
      exact p,
      assume q,

      -- law of the excluded middle
      have pornp := classical.em P,
      apply or.elim pornp,
        assume p,
        apply or.intro_left,
        exact p,

        assume np,
        apply or.intro_right,
        apply and.intro np q,

end


-- 8
theorem distrib_and_or : 
  ∀ (P Q R: Prop), (P ∨ Q) ∧ (P ∨ R) ↔
                    P ∨ (Q ∧ R) :=
begin
  assume P Q R,
  apply iff.intro _ _,
    assume porqandporr,
      have porq: P ∨ Q := and.elim_left porqandporr,
      have porr : P ∨ R := and.elim_right porqandporr,
      cases porq with p q,
      apply or.intro_left,
      exact p,
      cases porr with p r,
      apply or.intro_left,
      exact p,
      have qr : Q ∧ R := and.intro q r,
      apply or.intro_right,
      exact qr,

    assume porqandr,
    cases porqandr with p qandr,
    apply and.intro _ _,
      apply or.intro_left,
      exact p,
      apply or.intro_left,
      exact p,

    apply and.intro _ _,
      apply or.intro_right,
      exact and.elim_left qandr,
      apply or.intro_right,
      exact and.elim_right qandr,
end

-- remember or is right associative
-- you need this to know what the lefts and rights are
-- 9
theorem distrib_and_or_foil : 
  ∀ (P Q R S : Prop),
  (P ∨ Q) ∧ (R ∨ S) ↔
  (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S) :=
begin
  assume P Q R S,
  apply iff.intro _ _,
  --left
    assume porq_rors : (P ∨ Q) ∧ (R ∨ S),
    have porq : P ∨ Q := and.elim_left porq_rors,
    have rors : R ∨ S := and.elim_right porq_rors,

    cases porq,
      cases rors,
        apply or.intro_left,
        apply and.intro (porq) (rors),

        apply or.intro_right,
        have ps : P ∧ S := and.intro (porq) (rors),
        apply or.intro_left,
        exact ps,

      cases rors,
        have qr : Q ∧ R := and.intro (porq) (rors),
        
        apply or.intro_right,
        apply or.intro_right,
        apply or.intro_left,

        exact qr,


        have qs : Q ∧ S := and.intro (porq) (rors),

        apply or.intro_right,
        apply or.intro_right,
        apply or.intro_right,
        exact qs,


  --right
    assume pr_ps_qr_qs : (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S),
    apply and.intro _ _,
    cases pr_ps_qr_qs,
      have p : P := and.elim_left pr_ps_qr_qs,
      apply or.inl p,

    cases pr_ps_qr_qs,
      have p : P := and.elim_left pr_ps_qr_qs,
      apply or.inl p,

    cases pr_ps_qr_qs,
      have q : Q := and.elim_left pr_ps_qr_qs,
      apply or.inr q,

      have q : Q := and.elim_left pr_ps_qr_qs,
      apply or.inr q,
    


    cases pr_ps_qr_qs,
      have r : R := and.elim_right pr_ps_qr_qs,
      apply or.inl r,

    cases pr_ps_qr_qs,
      have s : S := and.elim_right pr_ps_qr_qs,
      apply or.inr s,

    cases pr_ps_qr_qs,
      have r : R := and.elim_right pr_ps_qr_qs,
      apply or.inl r,

      have s: S := and.elim_right pr_ps_qr_qs,
      apply or.inr s,

end


/- 10
Formally state and prove the proposition that
not every natural number is equal to zero.
-/
lemma not_all_nats_are_zero : ∀ (n : ℕ), (n=0) ∨ (n≠0) :=
begin
  assume n,
  apply classical.em,
end 

-- 11. equivalence of P→Q and (¬P∨Q)
example : ∀ (P Q : Prop), (P → Q) ↔ (¬P ∨ Q) :=
begin
  assume P Q,
  apply iff.intro _ _,
  --left
    assume pq : P → Q,

     -- law of the excluded middle
    have pornp : P ∨ ¬P := classical.em P,
    have qornq : Q ∨ ¬Q := classical.em Q,
    cases pornp,
      apply or.intro_right,
      cases qornq,
      apply qornq,
      apply pq pornp,

    cases qornq,
      apply or.intro_right,
      apply qornq,
      apply or.intro_left,
      apply pornp,

  --right
    assume nporq : ¬ P ∨ Q,
    assume p : P,

     -- law of the excluded middle
    have pornp := classical.em P,
    have qornq := classical.em Q,

    cases qornq,
      apply qornq,
      cases nporq,
        contradiction,
        apply nporq,

end

-- 12
example : ∀ (P Q : Prop), (P → Q) → (¬ Q → ¬ P) :=
begin
    assume P Q,
    assume pq : P → Q,
    assume nq : Q → false,

    /- Not necessary:

     -- law of the excluded middle
    have pornp : P ∨ ¬P := classical.em P,
    have qornq : Q ∨ ¬Q := classical.em Q,

    -/
    apply not.intro,
    assume p : P,
    have q : Q := pq p,
    contradiction,
  
end

-- 13
example : ∀ (P Q : Prop), ( ¬P → ¬Q) → (Q → P) :=
begin
  assume P Q,
  assume np_nq : ¬ P → ¬ Q,
  assume q : Q,

   -- law of the excluded middle
  have pornp : P ∨ ¬P := classical.em P,
  have qornq : Q ∨ ¬Q := classical.em Q,

  cases pornp,
    cases qornq,
    exact pornp,
    
    exact pornp,

  have nq : Q → false := np_nq pornp,
  contradiction,


end

