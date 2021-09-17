/-
Prove that equality is symmetric
-/
theorem eq_sym :
  ∀ (T : Type) (x y : T), x=y → y=x :=
  begin
    assume (T : Type), 
    assume (x y : T),
    assume ( e : x = y ),
    rw e,
  end

  /-
  English language proof of the above:
  Theorem: Equality is symmetric. In other words:
  ∀ (T : Type) (x y : T), x=y → y=x

  Proof: First we'll assume that T is any type and we have objects x and y of this type. What remains to be shown is that if x=y, then y=x. We'll assume the premise that x=y, and in this context, we need to prove that y=x. By the axiom of the susbstitutability of equals and by using the assumed fact that x=y, we can rewrite x in the goal as y, yielding y=x as our new proof goal. This is true by the axiom of reflexivity QED.
  -/

  /-
  Prove that equality is transitive
  -/

  theorem eq_trans :
  ∀ (T : Type) (x y z : T), x=y → y=z → x=z :=
  begin
    assume (T: Type),
    assume (x y z : T),
    assume (e1 : x = y),
    assume (e2 : y = z),
    rw e1,
    exact e2
  end