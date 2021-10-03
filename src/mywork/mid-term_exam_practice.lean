axiom eq_refl : ∀ (T : Type) (t : T), t = t

axiom eq_subst : ∀ (T : Type) (P : T → Prop) (x y : T) (e : x = y) (px : P x), P y

theorem eq_symm : ∀ (T : Type) (x y : T), x = y → y = x :=
begin
  assume T,
  assume x y,
  assume x_equals_y,
  apply eq.subst x_equals_y,
  apply eq.refl,
end

theorem eq_trans : ∀ (T : Type) (x y z : T), x = y → y = z → x = z :=
begin
  assume T,
  assume x y z,
  assume x_equals_y,
  assume y_equals_z,
  rw x_equals_y,
  exact y_equals_z,
end

-----
-- Implies intro rule:
-- Implies elim rule:
/-
(P Q : Prop) (pq : P → Q) (p : P)
--------------------------------- → elim
              q : Q
-/

-- Forall intro rule:
-- Forall elim rule:
/-
(T : Type) (P : T → Prop) (a : ∀ (x : T), P x) (t : T)
------------------------------------------------------ ∀ elim
                        pf: P t
-/

-----

/-
(P Q : Prop) (p : P) (q : Q)
---------------------------- ∧ intro
        ⟨p, q⟩ : P ∧ Q


(P Q : Prop) (pq : P ∧ Q)
------------------------- ∧ elim (left)
        p : P

(P Q : Prop) (pq : P ∧ Q)
------------------------- ∧ elim (right)
          q : Q

and is comm, and is assoc

-/

theorem and_commu : ∀ (P Q : Prop), P ∧ Q → Q ∧ P :=
begin
  assume P Q,
  assume p_and_q,
  cases p_and_q with p q,
  apply and.intro q p,
  --apply and.intro _ _,
  --apply and.elim_right p_and_q,
  --apply and.elim_left p_and_q,
end

theorem and_associ : ∀ (P Q R : Prop), P ∧ (Q ∧ R) → (P ∧ Q) ∧ R :=
begin
  assume P Q R,
  assume h,
  cases h with p qandr,
  cases qandr with q r,
  apply and.intro (and.intro p q) r,
  -- have
end

theorem and_associ2 : ∀ (P Q R : Prop), (P ∧ Q) ∧ R → P ∧ (Q ∧ R) :=
begin
  assume P Q R h,
  cases h with pandq r,
  cases pandq with p q,
  apply and.intro p (and.intro q r),
end

-- why no type arg for and
-- right assoc