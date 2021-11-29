
/-
Monday 11/29

Induction
-/

import algebra.algebra.basic tactic.ring

namespace hidden

inductive nat : Type -- declare type of "nat"
-- constructors
  | zero : nat                -- 0
  | succ (n' : nat) : nat     -- succesor of 0, assume that n' = n + 1

def z := nat.zero     -- zero
def o := nat.succ z   -- one
def t := nat.succ o   -- two

#check z
#reduce z
#reduce o
#reduce t

def f : nat := nat.succ (nat.succ t)   -- four

#reduce f

def inc1 : nat → nat :=    -- increment
begin
  assume n,
  exact nat.succ n,
end 

#reduce inc1 f     -- inc 4 -> 5


def inc2 : nat → nat
| n := nat.succ n

#reduce inc2 f    -- inc 4 -> 5


def dec : nat → nat
| (nat.zero) := nat.zero
| (nat.succ n') := n'


def add : nat → nat → nat
| (nat.zero) (m) := m
| (nat.succ n') (m) := nat.succ (add n' m)

#reduce add f f

def mul : nat → nat → nat
| (nat.zero) (m) := nat.zero
| (nat.succ n') (m) := add (m) (mul n' m)

#reduce mul t t


def exp : nat → nat → nat
| (m) (nat.zero) := nat.succ nat.zero
| (m) (nat.succ nat.zero) := m
| (m) (nat.succ n') := mul (n') (exp m n') 

#reduce exp t f


def sum_to : nat → nat
| (nat.zero) := nat.zero
| (nat.succ n') := add (sum_to n') (nat.succ n')

#reduce sum_to f

end hidden
