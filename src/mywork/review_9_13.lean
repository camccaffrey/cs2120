namespace implies
/-
Conditional proposition?
-/
axioms (P Q : Prop)
def if_P_is_true_then_so_is_Q : Prop := P → Q -- if p, then q


axiom p : P -- assume P is true, assume we have a proof of P (p)

axiom pq : P → Q  -- assume that we have a proof, pq, of P → Q 
                  -- intro rule for implies: assume premise, show conclusion
                  -- elimination rule for implies: 

#check pq
#check p
#check (pq p)

/-
Suppose P and Q are propositions and you know that P → Q and that P are both true. Show that P is true. 

Proof: Apply the truth of P → Q to the truth of P to derive the truth of Q.

Proof: By the elminination rule for → with pq applied to p.

Proof: By "modus ponens" QED
-/

/-
elimination rule of implies: you apply it?

-/
end implies



namespace all
/-
For All
-/

axioms
  (T : Type)
  (P : T → Prop) -- property P
  (t : T)
  (a : ∀ (x : T), P x)  -- proof a that all objects x of T, x has property P
                        -- elimination rule for "for all"

-- Does t have property P?
    -- yes

example: P t := a t

#check a t -- type: t has property P

end all



/-
AND & → 
-/

axioms (P Q : Prop)

/-
Want a proof of P ∧ Q. means proof that P is true and also that Q is true
-/