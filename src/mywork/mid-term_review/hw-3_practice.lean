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