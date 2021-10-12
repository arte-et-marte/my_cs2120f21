axioms
  (Person : Type)
  (Likes : Person → Person → Prop) -- Likes is a binary relation (using a 2-place predicate)

example: ¬(∀ (p : Person), Likes p p) ↔ ∃ (p : Person), ¬ Likes p p := -- uninhabitated type = no values/proofs/instances of that type
begin
  apply iff.intro _ _,
  -- forwards
  assume h,
  -- elim rule for all is simply to apply the all proof to something (of the correct type)
  have f := classical.em (∃ (p : Person), ¬Likes p p), -- how???
  cases f with f nf,
  -- case 1
  assumption,
  -- case 2 (how to unearth the contradiction???)
  have to_contra : ∀ (p : Person), Likes p p := _, -- come back to prove this after proving original goal
  contradiction,
  assume p,
  have lpp_nlpp := classical.em (Likes p p),
  cases lpp_nlpp with lpp nlpp,
  assumption,
  -- have a witness value and a proof that it can go into
  have a : ∃ (p : Person), ¬Likes p p := exists.intro p nlpp,
  contradiction,
  -- backwards
  
end