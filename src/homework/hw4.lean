-- 1
example : 0 ≠ 1 :=
begin
  -- 0 ≠ 1 => ¬(0 = 1),
  -- ¬(0 = 1) => (0 = 1) → false
  assume (h : 0 = 1),
  -- can also use 'trivial'
  contradiction, -- **COMMENT: You could have also used "cases" on your proof (of something that implies false) to obtain a proof of false.**
end

-- 2
example : 0 ≠ 0 → 2 = 3 :=
begin
  -- 0 ≠ 0 => 0 = 0 → false
  -- **?: 0 ≠ 0 → 2 = 3 => 0 = 0 → false → 2 = 3**
  assume h,
  -- have zeqz := eq.refl 0,
  -- contradiction,
  -- **COMMENT: Need to give h a proof of 0 = 0 (to get a proof of false).**
  have f : false := h (eq.refl 0),
  contradiction, -- **COMMENT: You could have also used "exact false.elim f,".**
end
-- **COMMENT: Whether you have a proof of false or you need a proof of false, you may be able to use "contradiction".**

-- 3
example : ∀ (P : Prop), P → ¬¬P := -- **COMMENT: Trying to prove that the existence of the proof of P means that there isn't NOT a proof of P.**
begin
  -- can CONSTRUCT a proof of double negation, don't need classical reasoning
  assume P,
  assume (p : P),
  assume h, -- **COMMENT: P → false is a premise to ¬¬P => (P → false) → false.** not not p just means not p implies false, so you can assume p
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
  assume h, -- h doesn't help us at all to get a proof of p, all we have left are our standalone props (P and Q), which we can use with the law of em
  -- ¬¬P => (P → false) → false // em says: there is a proof of ¬P, or there is not (P)
  have pornp := classical.em P, -- **COMMENT: Applying the axiom of the excluded middle to get a proof of P ∨ ¬P (to get a proof of P).**
  cases pornp with p np, -- **COMMENT: Performing case analysis (and assigning names to our assumed proofs).**
  assumption, -- **COMMENT: For the first case - applying our assumed proof of P to get a proof of P.**
  contradiction, -- **COMMENT: For the second case - pointing out that our axiom is being violated, we have a proof of ¬¬P and ¬P.**
end

-- 5
theorem demorgan_1 : ∀ (P Q : Prop), ¬(P ∧ Q) ↔ ¬P ∨ ¬Q :=
begin
  -- if p and q is false, then at least one of them is false
  -- if p or q is false, then there's no way p and q is true
  assume P Q,
  apply iff.intro _ _, -- could also use split
  -- forwards
  assume h, -- stuck? unless we look somewhere other than h...
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
  -- backwards
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
theorem demorgan_2 : ∀ (P Q : Prop), ¬(P ∨ Q) → ¬P ∧ ¬Q :=
begin
  assume P Q,
  assume h,
  cases (classical.em P) with p np,
  cases (classical.em Q) with q nq,
  -- case 1
  have porq := or.intro_left Q p,
  have f := h porq,
  exact false.elim f,
  -- case 2
  have porq := or.intro_left Q p,
  have f := h porq,
  exact false.elim f,
  -- case 3
  have q_or_nq := classical.em Q,
  cases q_or_nq with q nq,
  ---- subcase 1
  ---- subcase 2
  
  assume P Q,
  assume h,
  have np_or_nnp := classical.em ¬P,
  have nq_or_nnq := classical.em ¬Q,
  cases np_or_nnp with np nnp,
  cases nq_or_nnq with nq nnq,
  -- case 1:
  exact and.intro np nq,
  -- case 2:
  apply false.elim (h (_)),
  have q_or_nq := classical.em Q,
  cases q_or_nq with q nq,
  ---- subcase 1:
  exact or.intro_right P q, -- gave a proof of P ∨ Q to h
  ---- subcase 2:
  contradiction, -- no proof of P ∨ Q to give to h because there is a contradiction in context
  -- case 3:
  apply false.elim (h (_)),
  have p_or_np := classical.em P,
  cases p_or_np with p np,
  ---- subcase 1:
  exact or.intro_left Q p,
  ---- subcase 2:
  contradiction,
end

-- 7
theorem disappearing_opposite : 
  ∀ (P Q : Prop), P ∨ ¬P ∧ Q ↔ P ∨ Q := 
begin
  -- note for forwards: need just P to be true or Q to be true for P ∨ Q to be true
  assume P Q,
  apply iff.intro _ _,  
  -- forwards
  assume left,
  cases left with p np_and_q,
  ---- case 1:
  exact or.intro_left Q p,
  ---- case 2:
  exact or.intro_right P (and.elim_right np_and_q),
  -- backwards
  assume p_or_q,
  cases p_or_q with p q,
  -- case 1:
  exact or.intro_left (¬P ∧ Q) p,
  -- case 2:
  have p_or_np := classical.em P,
  cases p_or_np with p np,
  ---- subcase 1:
  exact or.intro_left (¬P ∧ Q) p,
  ---- subcase 2:
  apply or.intro_right P _,
  exact and.intro np q,
end

-- 8
theorem distrib_and_or : 
  ∀ (P Q R: Prop), (P ∨ Q) ∧ (P ∨ R) ↔
                    P ∨ (Q ∧ R) :=
begin
  -- need either a proof of P or a proof of Q and R (a proof of Q, a proof of R)
  assume P Q R,
  apply iff.intro _ _,
  -- forwards
  assume left,
  have p_or_q := and.elim_left left,
  have p_or_r := and.elim_right left,
  cases p_or_q with p q,
  ---- case 1
  exact or.intro_left (Q ∧ R) p,
  ---- case 2
  cases p_or_r with p r,
  ------ subcase 1
  exact or.intro_left (Q ∧ R) p,
  ------ subcase 2
  exact or.intro_right P (and.intro q r),
  -- backwards
  assume right,
  -- need a proof of porq AND a proof of porr
  apply and.intro _ _,
  apply or.elim right,
  ---- first goal
  assume p,
  exact or.intro_left Q p,
  ---- second goal
  assume qandr,
  exact or.intro_right P (and.elim_left qandr),
  -- backwards
  apply or.elim right,
  ---- first goal
  assume p,
  exact or.intro_left R p,
  ---- second goal
  assume qandr,
  exact or.intro_right P (and.elim_right qandr),
end

-- remember or is right associative
-- you need this to know what the lefts and rights are
-- 9
theorem distrib_and_or_foil : 
  ∀ (P Q R S : Prop),
  (P ∨ Q) ∧ (R ∨ S) ↔
  (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S) :=
begin
  -- ((P ∧ R) ∨ ((P ∧ S) ∨ ((Q ∧ R) ∨ (Q ∧ S))))
  assume P Q R S,
  apply iff.intro _ _,
  -- Forwards
  assume porq_and_rors,
  have porq := and.elim_left porq_and_rors,
  have rors := and.elim_right porq_and_rors,
  cases porq with p q,
  cases rors with r s,
  -- 1
  exact or.intro_left _ (and.intro p r),
  --2
  exact or.intro_right _ (or.intro_left _ (and.intro p s)),
  --3
  cases rors with r s,
  ---a
  exact or.intro_right _ (or.intro_right _ (or.intro_left _ (and.intro q r))),
  ---b
  exact or.intro_right _ (or.intro_right _ (or.intro_right _ (and.intro q s))),
  -- Backwards
  assume supercalifragilisticexpialidocious,
  apply and.intro _ _,
  -- first slot
  cases supercalifragilisticexpialidocious with pandr,
  ---- case 1
  exact or.intro_left Q (and.elim_left pandr),
  ---- case 2
  cases supercalifragilisticexpialidocious with pands,
  ------ subcase 1
  exact or.intro_left Q (and.elim_left pands),
  ------subcase 2
  cases supercalifragilisticexpialidocious with qandr,
  -------subcase of subcase 1
  exact or.intro_right P (and.elim_left qandr),
  -------subcase of subcase 2
  exact or.intro_right P (and.elim_left supercalifragilisticexpialidocious),
  --- case 3
  cases supercalifragilisticexpialidocious with pandr,
  ---- subcase 1
  exact or.intro_left S (and.elim_right pandr),
  ---- subcase 2
  cases supercalifragilisticexpialidocious with pands,
  ----- subsubcase 1
  exact or.intro_right R (and.elim_right pands),
  ----- subsubcase 2
  cases supercalifragilisticexpialidocious with qandr,
  ------ subsubsubcase 1
  exact or.intro_left S (and.elim_right qandr),
  ------ subsubsubcase 2
  exact or.intro_right R (and.elim_right supercalifragilisticexpialidocious),
end

#check nat.add 3
/- 10
Formally state and prove the proposition that
not every natural number is equal to zero.
-/
lemma not_all_nats_are_zero : ¬ ∀ (n : ℕ), (n = 0) :=
begin
  assume n,
  have f := n 1,
  contradiction
end 

-- 11. equivalence of P→Q and (¬P∨Q)
example : ∀ (P Q : Prop), (P → Q) ↔ (¬P ∨ Q) :=
begin
  assume P Q,
  apply iff.intro _ _,
  -- Forwards
  assume p_imp_q,
  have p_or_np : P ∨ ¬P := classical.em P,
  cases p_or_np with p np,
  ---- First case
  have q : Q := p_imp_q p,
  exact or.intro_right (¬P) q,
  ---- Second case
  exact or.intro_left Q np,
  -- Backwards
  assume np_or_q,
  cases np_or_q with np q,
  ---- First case
  assume p,
  contradiction, -- in my context!
  assume p,
  assumption,
end

-- 12
example : ∀ (P Q : Prop), (P → Q) → (¬ Q → ¬ P) :=
begin
  assume P Q,
  assume p_imp_q,
  have p_or_np := classical.em P,
  have q_or_nq := classical.em Q,
  cases p_or_np with p np,
  cases q_or_nq with q nq,
  -- 1
  assume nq,
  contradiction,
  -- 2
  have q := p_imp_q p,
  contradiction,
  -- 3
  cases q_or_nq with q nq,
  ---- a
  assume nq,
  contradiction,
  ---- b
  assume nq,
  exact np,
end

-- 13
example : ∀ (P Q : Prop), ( ¬P → ¬Q) → (Q → P) :=
begin
  assume P Q,
  assume np_imp_nq,
  have p_or_np := classical.em P,
  have q_or_nq := classical.em Q,
  cases p_or_np with p np,
  cases q_or_nq with q nq,
  -- 1
  assume q,
  assumption,
  -- 2
  assume q,
  contradiction,
  -- 3
  cases q_or_nq with q nq,
  ---- a
  have np := np_imp_nq np,
  contradiction,
  ---- b
  assume q,
  contradiction,
end