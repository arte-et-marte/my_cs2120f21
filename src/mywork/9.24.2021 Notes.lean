/-
Logical Connectives:
-- =:
---- Intro: Reflexivity of equality
---- Elim: Substitutability
-- ∧:
---- Intro: And intro 
-- ∨:
-- ∀:
---- Intro: assume, then show rest
---- Elim: apply
-- →:
-- ¬:
---- Intro: show P → false (assume we have a proof of false, then exact it)
---- Elim: ?
-- ↔:
---- Intro: 1
---- Elim: 2
-- ∃
-- true:
---- Intro: 1, true.intro
---- Elim: None
-- false:
---- Intro: 0,
---- Elim: false.elim
-/

/-
exam knowing them rules and what they mean
and how to use them-/

example : 0 ≠ 1 :=
begin
  -- ¬ (0 = 1)
  -- (0 = 1) → false
  assume h,
  cases h,
end

example : 0 ≠ 0 → 2 = 3 := -- Gonna need a contradiction, a proof of false
begin
  assume h,
  -- 0 = 0 → false : h is a proof of this. Given this proof, you can apply it
  exact false.elim (h (eq.refl 0)),
  -- false.elim (to a proof of false) (h (eq.refl 0)) <-- this is our proof of false, h is like a function that takes in 0 = 0.
  -- exact h (eq.refl 0),
end

example : ∀ (P : Prop), P → ¬¬P :=
begin
  assume P,
  -- ¬P = P → false
  -- ¬¬P = (P → false) → false
  -- P 
  assume p, -- (p : P)
  assume np, -- a proof of p and a proof of not p = a contradiction
  -- contradiction, -- or, alternatively,
  have f := np p, -- not p is a function!! it takes an arg of type P and gives you back false
  exact false.elim f, -- from a proof of false, get a proof of false, exact f would work too
end

-- if my dog is blue, it's false that my dog is not blue

theorem neg_elim : ∀ (P : Prop), ¬¬P → P :=
begin
  assume P,
  assume h,
  -- ¬P
  -- negation elimination: allows you to eliminate double
  -- negations, can have logic with/wo this axiom. to allow
  -- this, need to add this axiom - law of excluded middle
  -- stuck, unless use law of em to get proof of p or not p
  have pornp := classical.em P,
  -- p is now either true or false
  -- do case analysis
  cases pornp,
  exact pornp, -- or assumption
  -- have a contradiction in context, h and pornp
  contradiction,
end

axiom em : ∀ (p : Prop), P ∨ ¬P -- em is a function, give it any prop, gives you back a proof of p or not p, a proof of a disjunction, which you do case analysis on (thru elim rule), get stuck wo excluded middle axiom