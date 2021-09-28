-- 1
example : 0 ≠ 1 :=
begin
  -- 0 ≠ 1 => ¬(0 = 1),
  -- ¬(0 = 1) => (0 = 1) → false
  assume (h : 0 = 1),
  contradiction, -- **COMMENT: You could have also used "cases" on your proof (of something that implies false) to obtain a proof of false.**
end

-- 2
example : 0 ≠ 0 → 2 = 3 :=
begin
  -- 0 ≠ 0 => 0 = 0 → false
  -- **?: 0 ≠ 0 → 2 = 3 => 0 = 0 → false → 2 = 3**
  assume h,
  -- **COMMENT: Need to give h a proof of 0 = 0 (to get a proof of false).**
  have f : false := h (eq.refl 0),
  contradiction, -- **COMMENT: You could have also used "exact false.elim f,".**
end
-- **COMMENT: Whether you have a proof of false or you need a proof of false, you may be able to use "contradiction".**

-- 3
example : ∀ (P : Prop), P → ¬¬P := -- **COMMENT: Trying to prove that the existence of the proof of P means that there isn't NOT a proof of P.**
begin
  assume P,
  assume (p : P),
  assume h, -- **COMMENT: P → false is a premise to ¬¬P => (P → false) → false.**
  -- **COMMENT: Need to give h a proof of P (to get a proof of false).**
  have f : false := h p,
  contradiction, -- **COMMENT: You could have also used "exact f".**
end

-- We might need classical (vs constructive) reasoning
#check classical.em
open classical
#check em

/-
axiom em : ∀ (p : Prop), p ∨ ¬p

This is the famous and historically controversial
"law" (now axiom) of the excluded middle. It's is
a key to proving many intuitive theorems in logic
and mathematics. But it also leads to giving up on
having evidence *why* something is either true or
not true, in that you no longer need a proof of 
either P or of ¬P to have a proof of P ∨ ¬P.
-/

-- 4
theorem neg_elim : ∀ (P : Prop), ¬¬P → P :=
begin
  assume P,
  assume h,
  -- ¬¬P => (P → false) → false // em says: there is a proof of ¬P, or there is not (P)
  have pornp := classical.em P, -- **COMMENT: Applying the axiom of the excluded middle to get a proof of P ∨ ¬P (to get a proof of P).**
  cases pornp with p np, -- **COMMENT: Performing case analysis (and assigning names to our assumed proofs).**
  assumption, -- **COMMENT: For the first case - applying our assumed proof of P to get a proof of P.**
  contradiction, -- **COMMENT: For the second case - pointing out that our axiom is being violated, we have a proof of ¬¬P and ¬P.**
end

theorem porq : ∀ (P Q : Prop), P ∨ Q → true :=
begin
  assume P Q,
  assume porq,
  
end

theorem q_5_f : ∀ (P Q : Prop), ¬(P ∧ Q) → ¬P ∨ ¬Q :=
begin
  assume P Q,
  assume h,
  have p := h.left,
  assume P Q,
  assume h, -- ¬(P ∧ Q) => P ∧ Q → false // em says: there is a proof of P ∧ Q, or there is not (¬(P ∧ Q))
  apply false.elim (h (_)), -- "when you have a proof of an implication, you can apply it (to an argument of the right type)"
  have d := classical.em ¬P ∨ ¬Q,
  cases d,
end

theorem q_5_b : ∀ (P Q : Prop), ¬P ∨ ¬Q → ¬(P ∧ Q) :=
begin
  assume P Q,
  assume h,
  apply or.elim h,
  assume np,
  assume pandq, -- **?**
  cases pandq with p q,
  contradiction, -- in the context (have np and p)
  assume nq,
  assume pandq,
  cases pandq with p q,
  contradiction, -- in the context (have nq and q)
end

-- 6
theorem demorgan_2 : ∀ (P Q : Prop), ¬ (P ∨ Q) → ¬P ∧ ¬Q :=
begin
  assume P Q,
  assume h, -- ¬(P ∨ Q) => P ∨ Q → false
  have f := h _,
  contradiction,
  have d := classical.em (P ∨ Q),
  apply or.elim d,
  assume porq,
  exact porq, -- alternatively, "assumption"
  assume nporq,
  apply h 
  cases d,
end

-- 7
theorem disappearing_opposite : 
  ∀ (P Q : Prop), P ∨ ¬P ∧ Q ↔ P ∨ Q := 
begin
end


-- 8
theorem distrib_and_or : 
  ∀ (P Q R: Prop), (P ∨ Q) ∧ (P ∨ R) ↔
                    P ∨ (Q ∧ R) :=
begin
end

-- remember or is right associative
-- you need this to know what the lefts and rights are
-- 9
theorem distrib_and_or_foil : 
  ∀ (P Q R S : Prop),
  (P ∨ Q) ∧ (R ∨ S) ↔
  (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S) :=
begin
end


/- 10
Formally state and prove the proposition that
not every natural number is equal to zero.
-/
lemma not_all_nats_are_zero : _ :=
begin
end 

-- 11. equivalence of P→Q and (¬P∨Q)
example : ∀ (P Q : Prop), (P → Q) ↔ (¬P ∨ Q) :=
begin
end

-- 12
example : ∀ (P Q : Prop), (P → Q) → (¬ Q → ¬ P) :=
begin
end

-- 13
example : ∀ (P Q : Prop), ( ¬P → ¬Q) → (Q → P) :=
begin
end

