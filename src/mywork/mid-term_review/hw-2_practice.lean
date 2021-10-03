-- 14
example : ∀ (P : Prop), P ∧ false ↔ false :=
begin
  assume P,
  apply iff.intro _ _,
  -- forwards implication proof
  assume p_and_false,
  exact and.elim_right p_and_false,
  -- backwards implication proof
  assume f,
  exact false.elim f, -- **How does the false elim rule work?**
end

-- 12
example : ∀ (P : Prop), P ∨ false ↔ P :=
begin
  assume P,
  apply iff.intro _ _,
  -- forwards implication proof
  assume p_or_false,
  /-
  solution 1
  apply or.elim p_or_false,
  ---- case 1
  assume p,
  exact p, -- alternatively, 'assumption'
  ---- case 2
  assume f,
  exact false.elim f,
  solution 2
  -/
  cases p_or_false with p f, -- **What does 'cases' do?**
  assumption,
  exact false.elim f,
  -- backwards implication proof
  assume p,
  exact or.intro_left false p,
end

-- 10
example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P :=
begin
  assume P Q,
  apply iff.intro _ _,
  -- forwards implication proof
  assume p_or_pandq,
  /-
  solution 1
  apply or.elim p_or_pandq,
  ---- case 1
  assume p,
  exact p, -- alternatively, 'assumption'
  ---- case 2
  assume pandq,
  exact and.elim_left pandq,
  solution 2
  -/
  cases p_or_pandq with p pandq,
  assumption,
  exact and.elim_left pandq,
  -- backwards implication proof
  assume p,
  apply or.intro_left (P ∧ Q) p, -- **The 'or' intro rules take a proposition argument first, second a proof of a proposition.**
end

-- 9
example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P :=
begin
  assume P Q,
  apply iff.intro _ _,
  -- forwards implication proof
  assume p_and_porq,
  exact and.elim_left p_and_porq,
  -- backwards implication proof
  assume p,
  apply and.intro p _,
  exact or.intro_left Q p,
end