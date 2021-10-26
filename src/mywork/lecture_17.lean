import data.set

/-
We formally define two predicates on
natural numbers.
-/
def ev (n : ℕ) : Prop := n % 2 = 0
def od (n : ℕ) : Prop := ¬ ev n


/-
We now formally represent some sets.
Bear in mind that we represent a set
as a predicate, applicable to a value
of the member type, and "reducing to"
a proposition, possibly "about" that
value.

In the following example, among other
things, we see that set ℕ and ℕ → Prop
are (nearly) interchangeable as types. 
A set is its defined by its membership
predicate. The "nearly" is because you
get to use set notations when you use
set T rather than T → Prop to specify
the type of a set value.


Notations
  - display notation
      - used when we are working with a small number of values that we can enumerate each of
      - pair of curly braces with elements separated by commas
      - ex: {1, 2, 3, 4}
  - comprehension notation
      - set of ____ numbers "such that" ______
      - ex: { n : N | _ }
  
  - set ℕ is the same as ℕ → Prop, possibly??? 

-/

def empte : set ℕ := { n : ℕ | false }
  -- returns false for every natural number
  -- definition of the empty set (of natural numbers) because it is true for no natural numbers

def complete : set ℕ := { n : ℕ | true }
  -- set of all natural numbers (returns true for all numbers in the set of natural numbers)

def evens : set ℕ := { n : ℕ | ev n }
  -- apply ev predicate to n
  -- set of even natural numbers

def ods : set ℕ := { n : ℕ | od n }
  -- same as above, but for odd

def evens_union_ods : set ℕ := { n : ℕ | (ev n) ∨ (od n) }
  -- think "or" for ∪ 
  -- set of natural numbers that are even and/or odd (mutually exclusive in this case)

def evens_intersect_ods : set ℕ  := { n : ℕ | (ev n) ∧ (od n) }
  -- think "and" for ∩ 
  -- set of natrual numbers that are even AND odd (mutually exclusive in this case)

def evens_complement : set ℕ := { n : ℕ | ¬ ev n }
  -- think "not" for "complement"

def ods_complement : set ℕ := { n : ℕ | ¬ od n }

def evens_intersect_empty : set ℕ := { n : ℕ | ev n ∧ false}
  -- intersection of "evens" set and "empty" set
  -- returns the empty set because it is false for all n

def evens_intersect_complete : set ℕ := { n : ℕ | ev n ∧ true}
  -- intersection of "evens" set and "complete" set
  -- returns the set of even numbers (all n are in the complete set so it is irrelevant)

def evens_union_empty : set ℕ := { n: ℕ | ev n ∨ false}
  -- union of "evens" set and "empty" set
  -- returns the set of even numbers

def evens_union_complete : set ℕ := { n : ℕ | ev n ∨ true}
  -- union of "evens" set and "complete" set
  -- returns the complete set

-- fill in additional interesting combinations


/-
SET THEORY NOTATIONS
-/
/- empty set

Sometimes people use ∅ to represent the empty set
-/

#check ( ∅ : set ℕ )

/- set membership

A membership predicate applied to a value
yields a proposition: one that is true for
values in the set. The ∈ notation is just 
a shorthand for application of a membership
predicate to a value, but it gives a sense
of "inclusion" of a value in a collection
of values.
-/
#check evens 0        -- these are propositions
#check 0 ∈ evens
#check 1 ∈ evens

/- set difference

The difference between sets s1 and s2, 
written s1 \ s2, is the set of values
that are in s1 but not in s2. You can
think of this as the set s1 with the
elements in s2 "taken away." Sometimes
people use subtraction notation for
set difference: s1 - s2.
-/
#check evens \ ods         -- evens - odds = evens
#check evens \ evens       -- evens - evens = empty
#check evens \ empte       -- evens - empty = evens
#check evens \ complete    -- evens - complete = empty


/- complement

The complement of a set s is the set of all
values in the "universe of discourse" (in Lean,
a type) that are not in s. Lean doesn't provide
a notation, so we have to define it ourselves.
Here we define compl as the complement of a 
set of natural numbers.
-/

def compl_nat (s : set ℕ ) : set ℕ :=
{a | a ∉ s}

#check compl_nat evens

/- union
The union of two sets, s1 and s2, written
as s1 ∪ s2, is the set of elements that are 
in s1 or s2. 
-/

#check ods ∪ complete   -- complete
#check ods ∪ empte      -- ods
#check ods ∪ evens      -- complete 


/- intersection 

The intersection of two sets, s1 and s2, written
as s1 ∩ s2, is the set of elements that are in s1
and in s2.
-/

#check ods ∩ empte        -- empty 
#check evens ∩ complete   -- evens
#check ods ∩ evens        -- empty

/- product 

The product of two sets, (s1 : set T) and
(s2 : set V) is the set of all pairs (t, v),
where t ∈ s1 and v ∈ t2. People sometimes
use × to represent the set product operation.
In Lean we have to define it ourselves.
-/

def prodset {T V : Type} (s1 : set T) (s2 : set V) := 
  { pr : T × V | pr.1 ∈ s1 ∧ pr.2 ∈ s2 }

#check prodset evens empte    -- empty set of pr : T x V
#check prodset evens ods      --


/- subset

Given two sets, s1 and s2, of objects of some type 
T, we say that s1 is a subset of s2, written s1 ⊆ s2,
if every element in s1 is in s2. We say that s1 is a
proper subset of s2, written s1 ⊂ s2, if every value
in s1 is in s2 and some value in s2 is not in s1. 
-/

#check evens ⊆ evens
#check evens ⊂ evens              -- not true
#check evens ⊆ complete
#check evens ⊂ complete
#check evens ⊂ empte              -- not true
#check ∀ (s : set ℕ), empte ⊆ s


/- powerset

The powerset of a set, s, written 𝒫 s, is 
the set of all subsets of s. This makes the 
powerset a set of sets. 
-/

#check 𝒫 { 1, 2, 3}
#check 𝒫 evens


/-
Now let's state and prove some theorems.
-/


example : ∀ (n : ℕ), evens_union_ods n ↔ complete n := 
_


example : ∀ (n : ℕ), (n ∈ evens_union_ods) ↔ (n ∈ complete) := 
_


/-
Now we are in a position to see formal 
definitions of all of the preceding set
theory concepts.
-/

axioms (P Q : ℕ → Prop)

def pSet  : set nat := { n : ℕ | P n}
def qSet  : set nat := { n : ℕ | Q n}

#reduce 0 ∈ pSet
#reduce pSet ∪ qSet
#reduce pSet ∩ qSet
#reduce pSet \ qSet
#reduce pSet ⊆ qSet
#reduce 𝒫 pSet      -- harder to decipher


/-
Now that we understand these operations and
their corresponding notations in set theory,
we can start to state and prove theorems!
-/


