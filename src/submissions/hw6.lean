-- File: hw6.lean
-- Author: Connor McCaffrey (cam7qp)
-- Date: 10/27/2021

import data.set

/-
#1
Exercise: Prove that for any set, L, L ∩ L = L.
-/

example : ∀ {α : Type} (L : set α),  L ∩ L = L :=
begin
  assume α,
  assume L,
  apply set.ext _, -- rewrite the goal
  assume a,
  split,
  -- forwards
    assume aell,
    cases aell,
    exact aell_left,
  -- backwards
    assume ael,
    apply and.intro ael ael,
end 

/-
#2
Exercise: Give a formal statement and proof, then an 
English language proof, that the union operator on 
sets is commutative.
-/

example : ∀ {α : Type} (L X: set α),  L ∪ X = X ∪ L :=

/-
English Proof:
First, assume that sets L and X contain values of type α.
Because the axiom of set extensionalitiy says that sets
are equal if they contain the same elements, we can rewrite
our goal to  x ∈ L ∪ X ↔ x ∈ X ∪ L. This statement is
bidirectional, so we must apply the elimination rule of
"if and only if." In the forward direction, we must prove that
an element a of type α is in X ∪ L. Given that element a is
in L ∪ X, case analysis shows us that if a is in L, then it is
in X ∪ L, and if a is in X, it is in X ∪ L. In the backwards
direction, we must prove that an element a of type α is in L ∪ X.
Given that the element a is in X ∪ L, case analysis shows us
that if a is in X, then it is in L ∪ X, and if a in L, then
it is in L ∪ X. QED
-/

begin
  assume α,
  assume L,
  assume X,

  -- rewrite the goal
  apply set.ext _,
  assume a,

  split,
    -- forwards
      assume aexl,
      cases aexl,
        apply or.inr,
        assumption,

        apply or.inl,
        assumption,

    -- backwards
      assume aexl,
      cases aexl,
        apply or.inr,
        assumption,

        apply or.inl,
        assumption,
end

/-
#3
Exercise: Prove that ⊆ is reflexive and transitive.
Give a formal statement, a formal proof, and an English
language (informal) proof of this fact.
-/

example: ∀ (α : Type) (X Y Z : set α), ( X ⊆ Y → Y ⊆ Z → X ⊆ Z ) ∧ (X ⊆ X) :=

/-
English Proof:
First, assume that sets X Y Z contain values of type α. To
prove that ⊆ is both reflexive and transitive, we can proove
both of these propositions individually and then use the
introduction rule for and to reach our goal. To prove that ⊆
is transitve, we show that if X ⊆ Y and if Y ⊆ Z then X ⊆ Z.
We can assume that element a of type α exists and is in X.
Assuming that X ⊆ Y, then a is also in Y via the definition
of a subset. Assuming that X ⊆ Y, then a is also in Z via the
definition of a subset. Since this is true for any arbitrary a
in X, we can see that ⊆ is transitive. To show that X ⊆ X, we
must prove that if X is a set containing elements of type α,
then all values in X are also in X (the definiton of a subset).
This is just common sense according to our definition of a set.
Therefore, we can show that ⊆ is reflexive. QED
-/

begin
  assume α,
  assume X,
  assume Y,
  assume Z,

  apply and.intro _ _,
  -- left side
    assume xsuby,
    assume ysubz,
    assume a,
    assume aex,

    have aey := xsuby aex,
    have aez := ysubz aey,
    exact aez,
  
  -- right side
    assume a,
    assume aex,
    exact aex,
end

/-
#4
Exercise: Prove that ∪ and ∩ are associative.
Give a formal statement, a formal proof, and an 
English language (informal) proof of this fact.
-/

example:
∀ (α : Type) (X Y Z : set α), 
((X ∩ Y) ∩ Z = X ∩ (Y ∩ Z)) ∧
((X ∪ Y) ∪ Z = X ∪ (Y ∪ Z)) :=

/-
English Proof:
First, assume that X, Y, and Z are all sets containing
elements of type α. Because we want to proove that both
intersections and unions are associative, we can proove
each one individually and then apply the introduction
rule for and. To proove that intersection is associative,
we must show that (X ∩ Y) ∩ Z = X ∩ (Y ∩ Z). Because the
axiom of set extensionalitiy says that sets are equal if
they contain the same elements, we can rewrite our goal
to be x ∈ (X ∩ Y) ∩ Z ↔ x ∈ X ∩ (Y ∩ Z). This statement
is bidirectional, so we must apply the elimination rule of
"if and only if." In the forward direction, we can assume
an element a of type α is in (X ∩ Y) ∩ Z. Using
and (intersection) elimination, we can show that a is
in X, Y, and Z. Through and (intersection) introduction,
we can show that a is in Y ∩ Z and then X ∩ (Y ∩ Z).
In the backwards direction, we can assume an alement a of
type α is in X ∩ (Y ∩ Z). Using and (intersection) elimination,
we can show that a is in X, Y, and Z. Through
and (intersection) introduction, we can show that a is
in X ∩ Y and then (X ∩ Y) ∩ Z. Therefore, intersection is
associative. To proove that union is associative, we must show
that ((X ∪ Y) ∪ Z = X ∪ (Y ∪ Z)). Because the axiom of set
extensionalitiy says that sets are equal if they contain the
same elements, we can rewrite our goal to be
x ∈ (X ∪ Y) ∪ Z ↔ x ∈ X ∪ (Y ∪ Z). This statement is
bidirectional, so we must apply the elimination rule of
"if and only if." In the forward direction,we need to use
case analysis on if a is in X ∪ Y or if a is in Z. If a is
in Z, then it is also in Y ∪ Z and, by extension, X ∪ (Y ∪ Z)
via the or (union)introduction rule. If a is in X ∪ Y, we
need to use case analysis on if a is in X or if a is in Y.
If a is in X, then it is in X ∪ (Y ∪ Z) via or (union) introduction.
If a is in Y, then it is in Y ∪ Z and, by extension X ∪ (Y ∪ Z)
via or (union) introduction. In the backward direction, we need
to use case analysis on if a is in X or if a is in Y ∪ Z. If a is
in X, then it is also in X ∪ Y and, by extension, (X ∪ Y) ∪ Z
via the or (union) introduction rule. If a is in Y ∪ Z, we need
to use case analysis on if a is in Y or if a is in Z. If a is
in Z, then it is in (X ∪ Y) ∪ Z via or (union) introduction.
If a is in Y, then it is in X ∪ Y and, by extension (X ∪ Y) ∪ Z
via or (union) introduction. Therefore, union is associative.
Putting everything together using and introduction, we now have
proof that both intersection and union are associative. QED
-/

begin
  assume α,
  assume X,
  assume Y,
  assume Z,
  
  apply and.intro _ _,
  -- left side
    apply set.ext _, -- rewrite the goal
    assume a,
    split,
    -- forwards
      assume aexyz,

      have aexy := and.elim_left aexyz,
      have aex := and.elim_left aexy,
      have aey := and.elim_right aexy,
      have aez := and.elim_right aexyz,

      have aeyz := and.intro aey aez,
      exact and.intro aex aeyz,

    -- backwards
      assume aexyz,

      have aex := and.elim_left aexyz,
      have aeyz := and.elim_right aexyz,
      have aey := and.elim_left aeyz,
      have aez := and.elim_right aeyz,

      have aexy := and.intro aex aey,
      exact and.intro aexy aez,

  -- right side
  apply set.ext _, -- rewrite the goal
  assume a,
  split,
  -- forwards
    assume aexy,
    cases aexy,
    -- left
      cases aexy,
      -- left -> left
        apply or.inl,
        apply aexy,

      -- left -> right
        apply or.inr,
        apply or.inl,
        apply aexy,
      
    -- right
      apply or.inr,
      apply or.inr,
      apply aexy,

  -- backwards
    assume aeyz,
    cases aeyz,
      -- left
        apply or.inl,
        apply or.inl,
        apply aeyz,

      -- right
        cases aeyz,

        -- right -> left
          apply or.inl,
          apply or.inr,
          apply aeyz,
        
        -- right -> right
        apply or.inr,
        apply aeyz,
end

/-
Assignment: read (at least skim) the Sections 1 and 2 of 
the Wikipedia page on set identities: 
https://en.wikipedia.org/wiki/List_of_set_identities_and_relations 
There, , among *many* other facts, you will find definitions 
of left and right distributivity. To complete the remainder
of this assignment, you need to understand what it means for 
one operator to be left- (or right-) distributive over another. 
-/


/-
#5
Exercise: Formally state and prove both formally and 
informally that ∩ is left-distributive over ∩.
-/

example: ∀ (α : Type) (X Y Z : set α), X ∩ (Y ∩ Z) = (X ∩ Y) ∩ (X ∩ Z) :=

/-
English proof:
First, assume that X, Y, and Z are all sets containing elements
of type α. Because we are trying to proove that ∩ is left-distributive
over ∩, we must show that  X ∩ (Y ∩ Z) = (X ∩ Y) ∩ (X ∩ Z).
Because the axiom of set extensionalitiy says that sets are equal
if they contain the same elements, we can rewrite our goal to
be x ∈ X ∩ (Y ∩ Z) ↔ x ∈ X ∩ Y ∩ (X ∩ Z). This statement is
bidirectional, so we must apply the elimination rule of
"if and only if." In the forward direction, we can assume that an
element a of type α is in X ∩ (Y ∩ Z). Using and (intersection) elimination,
we can show that a is in X, Y, and Z. Through and (intersection) introduction,
we can show that a is in X ∩ Y, X ∩ Z, and then (X ∩ Y) ∩ (Y ∩ Z).
In the backward direction, we can assume that an element a of type α
is in (X ∩ Y) ∩ (X ∩ Z). Using and (intersection) elimination, we can
show that a is in X ∩ Y, X ∩ Z, and then individually in X, Y, and Z.
Through and (intersection) introduction, we can show that a is
in Y ∩ Z and, by extension, X ∩ (Y ∩ Z). Thus, ∩ is left-distributive
over ∩. QED
-/

begin
  assume α,
  assume X,
  assume Y,
  assume Z,

  -- rewrite the goal
  apply set.ext _,

  assume a,
  split,
  -- forwards
    assume aexyz,

    -- and elimination
    have aex := and.elim_left aexyz,
    have aeyz := and.elim_right aexyz,
    have aey := and.elim_left aeyz,
    have aez := and.elim_right aeyz,

    -- and introduction
    have aexy := and.intro aex aey,
    have aexz := and.intro aex aez,
    have aexyxz := and.intro aexy aexz,

    exact aexyxz,

  -- backwards
    assume aexyxz,

    -- and elimination
    have aexy := and.elim_left aexyxz,
    have aexz := and.elim_right aexyxz,
    have aex := and.elim_left aexy,
    have aey := and.elim_right aexy,
    have aez := and.elim_right aexz,

    -- and introduction
    have aeyz := and.intro aey aez,
    have aexyz := and.intro aex aeyz,

    exact aexyz,
end

/-
#6
Exercise: Formally state and prove both formally 
and informally that ∪ is left-distributive over ∩.
-/

example: ∀ (α : Type) (X Y Z : set α), X ∪ (Y ∩ Z) = (X ∪ Y) ∩ (X ∪ Z) :=

/-
English proof:
First, assume that X, Y, and Z are all sets containing
elements of type α. Because we are trying to proove that
∪ is left-distributive over ∩, we must show that
X ∪ (Y ∩ Z) = (X ∪ Y) ∩ (X ∪ Z). Because the axiom of set
extensionalitiy says that sets are equal if they contain
the same elements, we can rewrite our goal to be
x ∈ X ∪ Y ∩ Z ↔ x ∈ (X ∪ Y) ∩ (X ∪ Z). This statement is
bidirectional, so we must apply the elimination rule of
"if and only if." In the forward direction, we can assume
that an element a of type α is in X ∪ (Y ∩ Z). We will need
to use case analysis on if a is in X or a is in Y ∩ Z. If a
is in X, then it is in both X ∪ Y and X U Z via
or (union) introduction. Then, by the introduction rule of
and (intersection), a is in (X ∪ Y) ∩ (X ∪ Z). If a is
in Y ∩ Z, then we can apply and (intersection) elimination
to show that a is in both Y and Z. From here, we can see that
if a is in Y, then it is in X ∪ Y via or (union) introduction.
Similarly, we can see that if a is in Z, then it is in X ∪ Z
via or (union) introduction. Then, by the introduction rule of
and (intersection), a is in (X ∪ Y) ∩ (X ∪ Z). In the backward
direction, we can assume that an element a of type α is in
(X ∪ Y) ∩ (X ∪ Z). We can use and (intersection) elimination to
show that a is in both X ∪ Y and X ∪ Z. We will need to use case
analysis on if a is in X or if a is not in X. If a is in X, then
by or (union) introduction, a is in X ∪ (Y ∩ Z). If a is not
in X, then for a to be in X ∪ Y, it must be true that a is
in Y. Similarly, for a to be in X ∪ Z, it must be true that a is
in Z. Given that a is in Y and Z, we can use the introduction rule
of and (intersection) to show that a is in Y ∩ Z. Using
or (union) introduction, we can then show that a is in X ∪ (Y ∩ Z).
Thus, we now have proof that ∪ is left-distributive over ∩. QED
-/

begin
  assume α,
  assume X,
  assume Y,
  assume Z,

  apply set.ext _, -- rewrite the goal
  assume a,
  split,
  -- forwards
    assume aexyz,
    cases aexyz,
      -- left
        apply and.intro _ _,
          apply or.inl aexyz,
          apply or.inl aexyz,
      
      -- right
        apply and.intro _ _,
          have aey := and.elim_left aexyz, --aeyz
          apply or.inr aey,

          have aez := and.elim_right aexyz, --aeyz
          apply or.inr aez,

  -- backwards 
    assume aexyxz,

    have aexy := and.elim_left aexyxz,
    have aexz := and.elim_right aexyxz,

    apply or.elim aexy,
    -- left
      assume aex,
      exact or.inl aex,

    -- right
      assume aey,

    apply or.elim aexz,
    -- left
      assume aex,
      exact or.inl aex,

    -- right
      assume aez,
    
    have aeyz := and.intro aey aez,
    exact or.inr aeyz,
end
