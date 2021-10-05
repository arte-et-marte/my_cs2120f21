-- Is the exam open-note?
-- What does lemma mean?

/-
exists intro takes in two things _ _
- a witness, 3
- proof that 3 satisfies predicate

∃ (n : ℕ), ev n
exists.intro 

3 ways to get to a goal of false:
1. some var of type false, can exact it (or contradiction?)
2. apply false elimination rule on a proof of false.
3. have 2 variables that provide a direct contradiction in context
4. have a proof of something's that's obviously false, 1 = 0, can apply cases to that, 0 cases
-/

example : ∃ (n : ℕ), n = 1 :=
begin
  -- how do we prove an exists statement - need the exists Intro rule!
  exact exists.intro 1 (eq.refl 1),
end

