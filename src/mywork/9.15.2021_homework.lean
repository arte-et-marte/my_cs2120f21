/-
1) Prove that or is commutative.
-/
theorem or_is_comm :
  ∀ (P Q : Prop) (q : Q), P ∨ Q → Q ∨ P :=
    begin
      assume P Q q p_or_q,
      exact or.intro_left P q,
    end

/-
2) Prove that or is associative.
-/
theorem or_is_assoc :
  ∀ (P Q R : Prop) (p : P), (P ∨ Q) ∨ R → P ∨ (Q ∨ R) :=
    begin
      assume P Q R p pq_r,
      exact or.intro_left (Q ∨ R) p,
    end