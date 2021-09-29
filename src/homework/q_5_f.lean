theorem q_5_f : ∀ (P Q: Prop), ¬(P ∧ Q) → ¬P ∨ ¬Q :=
begin
  assume P Q,
  assume h,
  have p_or_np := classical.em P,
  have q_or_nq := classical.em Q,
  cases p_or_np with p np,
  cases q_or_nq with q nq,
  -- case 1:
  have pandq := and.intro p q,
  have f := h pandq,
  exact false.elim f,
  -- case 2:
  exact or.intro_right (¬P) nq,
  -- case 3:
  exact or.intro_left (¬Q) np,
end