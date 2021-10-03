-- 1
example : 0 ≠ 1 :=
begin
  assume zero_eq_one,
  contradiction, -- **Cannot construct a proof of false.**
end

-- 2
example : 0 ≠ 0 → 2 = 3 :=
begin
  assume zero_neq_zero,
  exact false.elim (zero_neq_zero (eq.refl 0)), -- **zero_neq_zero (0 = 0) does not construct a proof of false because (0 = 0) is a proposition not a proof.**
end

-- 3
example : ∀ (P : Prop), P → ¬¬P :=
begin
  assume P,
  assume p,
  assume np, -- **Translate 'not's' to "...implies false".**
  contradiction,
end

-- 4
theorem neg_elim : ∀ (P : Prop), ¬¬P → P :=
begin
  assume P,
  assume nnp,
  have p_or_np : P ∨ ¬P := classical.em P, -- **Introducing a proof of the disjunct P ∨ ¬P to show that the truthness of either will yield a proof of ¬¬P or a proof of false (from which anything follows).**
  cases p_or_np with p np,
  exact p,
  contradiction,
end

-- 5
theorem demorgan_1 : ∀ (P Q : Prop), ¬(P ∧ Q) ↔ ¬P ∨ ¬Q :=
begin
  assume P Q,
  apply iff.intro _ _,
  -- forwards implication proof
  assume n_pandq,
  have p_or_np : P ∨ ¬P := classical.em P,
  cases p_or_np with p np,
  have q_or_nq : Q ∨ ¬Q := classical.em Q,
  cases q_or_nq with q nq, -- **Why do we get three cases?**
  have f : false := n_pandq (and.intro p q),
  exact false.elim f,
  exact or.intro_right (¬P) nq,
  exact or.intro_left (¬Q) np,
  -- backwards implication proof
  assume np_or_nq,
  assume p_and_q,
  cases np_or_nq with np nq,
  have p : P := and.elim_left p_and_q,
  contradiction,
  have q : Q := and.elim_right p_and_q,
  contradiction,
end

-- 6
theorem demorgan_2 : ∀ (P Q : Prop), ¬(P ∨ Q) → ¬P ∧ ¬Q :=
begin
  assume P Q,
  assume n_porq,
  have np_or_nnp : ¬P ∨ ¬¬P := classical.em ¬P,
  cases np_or_nnp with np nnp,
  have nq_or_nnq : ¬Q ∨ ¬¬Q := classical.em ¬Q,
  cases nq_or_nnq with nq nnq,
  -- case 1
  exact and.intro np nq,
  -- case 2 **TRICKY!!!**
  apply false.elim (n_porq _),
  have q_or_nq : Q ∨ ¬Q := classical.em Q,
  cases q_or_nq with q nq,
  ---- subcase 1
  exact or.intro_right P q,
  ---- subcase 2
  contradiction,
  -- case 3 **Remember: You are trying to show a contradiction (get a proof by negation) by means the false elimination rule.**
  apply false.elim (n_porq _),
  have p_or_np : P ∨ ¬P := classical.em P,
  cases p_or_np with p np,
  ---- subcase 1
  exact or.intro_left Q p,
  ---- subcase 2
  contradiction,
end

-- 10
theorem not_all_nats_are_zero : ¬(∀ (n : ℕ), n = 0) :=
begin
  assume prop,
  have f := prop 1, -- **Not 'have f : false := prop 1' because it's not a proof of false that prop 1 should return; it should return a proof of n = 1.**
  contradiction,
end