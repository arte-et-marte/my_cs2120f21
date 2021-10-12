/-
Social Networks
-/

axioms
  (Person : Type)
  (Nice : Person → Prop)
  (Likes : Person → Person → Prop)

/-
What does this say, in English? It is true?
-/
example : 
  -- If there's a person, p1, who everyone likes,
  (∃ (p1 : Person), ∀ (p2 : Person), Likes p2 p1) → 
  -- then everyone likes someone
  (∀ (e : Person), ∃ (s : Person), Likes e s) :=
begin
  assume h,
  cases h with p pf,
  assume e,
  apply exists.intro p,
  exact (pf e),
end