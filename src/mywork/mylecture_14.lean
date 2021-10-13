
axioms
  (Person : Type)
  (Likes : Person → Person → Prop) --likes is a binary relation with two place predicate
                                   --set of pairs
                                   --means to like yourself???
example :
  ¬ (∀ p : Person, Likes p p) ↔ ∃ p : Person, ¬ Likes p p :=
  -- if it is false that all people like themselves, then there exists a person that does not like themselves
begin
  apply iff.intro,
  --left
    assume h,
    have f := classical.em (∃ (p : Person), ¬ Likes p p),
    cases f,
      assumption,
      have contra : ∀ (p : Person), Likes p p := _,
      contradiction,
      
    assume p,
    
    have g := classical.em (Likes p p),
    cases g,
    assumption,

    have a : ∃ (p : Person), ¬Likes p p := exists.intro p g, contradiction,

  --right
    assume h,
    cases h with p Q,


end