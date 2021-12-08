/-
File: homework_final.lean
Name: Connor McCaffrey (cam7qp), github.com/camccaffrey
Date: 12/8/2021
-/

/-
Read, understand (collaborating if necessary) the material
in chapter 17 of Jeremy Avigad's *Logic and Proof.* It's here:
https://leanprover.github.io/logic_and_proof/the_natural_numbers_and_induction.html
-/
import algebra.algebra.basic
import tactic.ring
/-
The following problems are listed in the Problems section of 
the chapter. 
-/


/-
#1. Solve probem #1, first sentence only.

Principle of Complete Induction:
  Let P be any property that satisfies the following: for any natural number n,
  whenever P holds of every number less than n, it also holds of n. Then P
  holds of every natural number.

Principle of Complete Induction in Symbolic Logic:
-/
def P : ℕ → Prop := sorry

def complete_induction := 
∃ (n : ℕ), ∀ (m : ℕ), m < n → P n → P m → ∀ (k : ℕ), P k





/-
#2. Solve at least one of #2 and #3. Give detailed but informal proofs. 

Informal Proof for Exercise #2 - Sum of Squares

Show that for every n, 
0² + 1² + 2² + … + n² = n(1 + n)(1 + 2n) / 6

Note: this can be rewritten as ∑ i² [0, n]
0² + 1² + 2² + … + n² = ∑ i² [0, n] = n(1 + n)(1 + 2n) / 6

To prove this inductively, we first define a base case where n = 0. 
LHS = ∑ 0² [0, 0] = 0
RHS = (0)(1 + 0)(1 + 2(0)) / 6 = 0
LHS = RHS = 0

Since we have proven the statement is true when n = 0, we now need to
prove that it is true fora all n > 0. For this, we use the inductive case.
In the inductive case, we assume the inductive hypothesis but replace n with (n+1):

IH with n:      0² + 1² + 2² + … + n² = ∑ i² [0, n] = n(1 + n)(1 + 2n) / 6
IH with (n+1):  0² + 1² + 2² + … + n² + (n+1)² = ∑ i² [0, n+1] = (n + 1)(2 + n)(3 + 2n) / 6

Show that the RHS = LHS
LHS:
  ∑ i² [0, n+1] = ∑ i² [0, n] + (n+1)²
                = n(1 + n)(1 + 2n) / 6  +  (n+1)²
                = (n(1 + n)(1 + 2n) + 6(n + 1)²) / 6
                = (n+1) * (n(1+2n) + 6(n+1)) / 6

RHS:
  ∑ i² [0, n+1] = (n + 1)(2 + n)(3 + 2n) / 6


Set RHS equal to LHS:
  (n + 1)(2 + n)(3 + 2n) / 6 = (n+1) (n(1+2n) + 6(n+1)) / 6
  (n + 1)(2 + n)(3 + 2n) = (n+1) * (n(1+2n) + 6(n+1))
  (2 + n)(3 + 2n) = n(1 + 2n) + 6(n + 1)
  6 + 3n + 4n + 2n² = n + 2n² + 6n + 6
  2n² + 7n + 6 = 2n² + 7n + 6

.: LHS = RHS = 2n² + 7n + 6

As shown above, the inductive hypothesis holds in
both cases. Thus, we have proven by induction that
for all n, ∑ i² [0, n] = n(1 + n)(1 + 2n) / 6 
-/





/-
To test out of the final exam ...

#1: Give a formal proof for #2 or #3.
-/

-- The following are formal proofs for both Exercises #2 and #3
def sum_of_sqrs : nat → nat
-- ∑ i² [0, n]
| (nat.zero) := (nat.zero)
| (nat.succ n') := nat.add (sum_of_sqrs n')  (nat.mul (nat.succ n') (nat.succ n'))


def sum_of_cubes : nat → nat
-- ∑ i³ [0, n]
| (nat.zero) := (nat.zero)
| (nat.succ n') := (nat.add (sum_of_cubes n') (nat.mul (nat.succ n') (nat.mul (nat.succ n') (nat.succ n'))))


def P_sum_sqrs : ℕ → Prop :=
-- sum_of_sqrs property:
    --   ∑ i² [0, n] = (n * (n+1) * (2n+1)) / 6
    -- 6 ∑ i² [0, n] = n * (n+1) * (2n+1)
  λ n, 
  nat.mul (6) (sum_of_sqrs n) =     --manipulate equation to avoid division by 6
  nat.mul (n) (nat.mul (nat.add n 1) (nat.add (nat.mul 2 n) (1)))


def P_sum_cubes : ℕ → Prop :=
-- sum_of_cubes property
    --   ∑ i² [0, n] = (n² * (n+1)²) / 4
    -- 4 ∑ i² [0, n] = n² * (n+1)²
  λ n,
  nat.mul (4) (sum_of_cubes n) =    --manipulate equation to avoid division by 4
  nat.mul (nat.mul (n) (n)) (nat.mul (nat.add n 1) (nat.add n 1))


-- Sum of Squares Proof by Induction
example : ∀ (m : ℕ), P_sum_sqrs m :=
begin
  unfold P_sum_sqrs,
  assume m,

  induction m with m' ih,
  apply rfl,

  simp [sum_of_sqrs],
  simp [nat.mul] at ih,
  rw [mul_add, ih, nat.succ_eq_add_one],

  ring,
end


-- Sum of Cubes Proof by Induction
example : ∀ (m : ℕ), P_sum_cubes m :=
begin
  unfold P_sum_cubes,
  assume m,

  induction m with m' ih,
  apply rfl,

  simp [sum_of_cubes],
  simp [nat.mul] at ih,
  rw [mul_add, ih, nat.succ_eq_add_one],

  ring,
end


/-
#2: Formal or detailed informal proofs 10-13
-/

-- #10. ∀ n, 1 * n = n
def nat_mult : nat → nat → nat
| (m) (nat.zero) := (nat.zero)
| (m) (nat.succ n') := nat.add (nat_mult m n') (m)


def P_mult : ℕ → Prop :=
  λ n,
  nat_mult 1 n = n


example : ∀ (m : ℕ), P_mult m :=
begin
  unfold P_mult,
  assume m,

  induction m with m' ih,
  exact rfl,

  rw nat.succ_eq_add_one,
  simp [nat_mult],
  
  apply ih,
end





-- #11. ∀ m n k, m(n+k) = mn + mk
def P_distributive : ℕ → ℕ → ℕ → Prop :=
  λ m n k,
  nat.mul (m) (nat.add n k) = nat.add (nat.mul m n) (nat.mul m k)


example : ∀ (m n k : ℕ), P_distributive m n k :=
begin
  unfold P_distributive,
  
  assume m,
  assume n,
  assume k,

  induction m with m' ih,

  simp [nat.mul],
  simp [nat.add],
  simp [nat.succ_eq_add_one],
  simp [nat.mul] at ih,

  ring,
end




-- #12. multiplication is associative
def mult_associative : ℕ → ℕ → ℕ → Prop :=
-- (m * n) * k = m * (n * k)
  λ m n k,
  nat.mul (nat.mul m n) (k) = nat.mul (m) (nat.mul n k)


example : ∀ (m n k : ℕ), mult_associative m n k :=
begin
  unfold mult_associative,

  assume m,
  assume n,
  assume k,

  induction m with m' ih,

  simp [nat.mul],
  simp [nat.add],
  simp [nat.succ_eq_add_one],
  simp [nat.mul] at ih,

  ring
end





-- #13. multiplication is commutative
def mult_commutative : ℕ → ℕ → Prop :=
-- m * n = n * m
  λ m n ,
  nat.mul m n = nat.mul n m


example : ∀ (m n : ℕ), mult_commutative m n :=
begin
  unfold mult_commutative,

  assume m,
  assume n,

  induction m with m' ih,
  
  simp [nat.mul],
  simp [nat.succ_eq_add_one],
  simp [nat.mul] at ih,

  ring,
end


/-
#3 (Extra Credit): #5 or #9
NOT FINALIZED. ADVISORY. 
-/
