/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.
-/

-- #1
example : true := true.intro
/-
True is true by its introduction rule.
-/

-- #2
example : false := _
/-
A proof cannot be constructed for false.
-/

-- #3
example : ∀ (P : Prop), P ∨ P ↔ P := -- P or P implies P AND P implies P or P
begin
  assume P,
  apply iff.intro _ _, -- two proofs, for both directions
  -- forward
    assume porp, --using implies intro rule...assume we have premise
    -- look  at  (prove) both cases, how we use a proof of a disjunction
    apply or.elim porp,
    -- left disjunct is true
    assume p, /-to prove P → P-/
    exact p,
    -- right disjunct is true
    assume p,
    exact p,
  -- backward
  assume p,
  exact or.intro_right P p
end
-- p or p is true, then case analysis left and right which are p is t / forward implication only true if prev is met
-- now for backwards dir
/-
First, we assume that we have a arbitrary proposition,
P, and apply the "ifandonlyif" introduction rule to
obtain the two proofs that we need - one for each
direction.

The proof P ∨ P → P is begun by applying the "implies"
introduction rule, by which we assume that the left-hand
side of our proposition is true. To this, we then apply
the "or" elimation rule, which allows us to use our proof
of the aforementioned disjunction to perform case
analysis. For the first case, we assume that P is true
("implies" introduction rule) and apply that proof/truth.
We do the same for the second case.

The proof of P → P ∨ P is also begun with the "implies"
introduction rule, by which we assume that we have a
proof of P. We then use this proof of P and the
proposition P with the "or" introduction rule to obtain
the needed proof of P.-/

-- assume we have a proof of P, p

-- #4
example : ∀ (P : Prop), P ∧ P ↔ P :=
begin
  assume P,
  apply iff.intro _ _,
  -- forward
  assume pandp,
  apply and.elim_left pandp,
  -- backward
  assume p, -- implies intro rule is just assuming the premise is true
  apply and.intro p p,
end
/-
Paste.

The proof of P ∧ P → P is begun by assuming that P ∧ P
is true through the "implies" introduction rule. With
this, we may start working on our proof of P. We prove
P by applying the left "and" elimination rule on our
proof of P ∧ P, pandp, which gives to us a proof of P.

The proof of P → P ∧ P is started by assuming that P is
true. To prove an "and" proposition, we need both sides
of the proposition to be true, so we apply the "and"
introduction rule to the proofs of P.
-/

-- #5
example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P :=
begin
  assume P Q,
  apply iff.intro _ _,
  -- forward
  assume porq,
  apply or.elim porq,
  assume p,
  apply or.intro_right Q p,
  assume q,
  apply or.intro_left P q,
  -- backward
  assume qorp, -- using the implies logical connective intro rule (simply assuming that the left side of your proposition is true)
  apply or.elim qorp, -- to prove that Q ∨ P → P ∨ Q, I need either Q to be true OR P to be true. I have to SHOW that that can be the case by proving each case. (Case analysis)
  assume q,
  apply or.intro_right P q,
  assume p,
  apply or.intro_left Q p,
end
/-
Paste.

The proof of P ∨ Q → Q ∨ P starts by assuming that our
P ∨ Q proposition is true ("implies" introduction rule).
We must then apply the "or" elimination rule to our
proof of the aforementioned proposition to perform case
analysis, where we show that in either case (P is true
or Q is true) our conclusion will be true. For the first
case we assume P, and to get our proof of the larger
"or" proposition we use the right "or" introduction rule
on our proposition Q and our assumed P. For the second
case we assume Q and use the left "or" introduction rule
on our proposition P and our assumed Q.

The proof of Q ∨ P → P ∨ Q begins by assuming our
premise. The "or" elimination rule is used on our
(assumed) proof of the premise. With that, we start on
our first case by assuming a proof of Q and generating
the needed proof with the right "or" introduction rule
on the proposition P and the proof of Q. We account
for the second case by assuming a proof of P and using
the left "or" introduction rule on the proposition Q
and our proof of P.
-/

-- #6
example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P :=
begin
  assume P Q,
  apply iff.intro _ _,
  -- forward
  assume pandq,
  -- now, to prove Q ∧ P, I need a proof of Q AND a proof of P
  apply and.intro _ _,
  apply and.elim_right pandq, -- fills in the first slot above with a proof of Q
  apply and.elim_left pandq, -- fills in the second slot above with a proof of P
  -- backward
  assume qandp, -- assuming that the left side of my proposition is true (the proposition: Q ∧ P → P ∧ Q)
  apply and.intro _ _,
  apply and.elim_right qandp,
  apply and.elim_left qandp,
end
/-
Paste.

To prove that if P ∧ Q, then Q ∧ P, first assume that
P ∧ Q is true by the "implies" introduction rule. To
prove an "and" proposition, we need to have two proofs -
one for each side of the "and". As such, we use the
right "and" elimination rule to get a proof of Q and the
left "and" elimination rule to get a proof of P. The "and"
introduction rule uses these two proofs to give us a proof
of the larger "and" proposition, Q ∧ P.

Proving that if Q ∧ P, then P ∧ Q requires that we first
assume that Q ∧ P is true (we have a proof of this). We
follow a similar process to the one above by using the
right "and" elimination rule to get a proof of P from our
assumed proof of the premise and the left "and"
elimination rule to get a proof of Q. The "and"
introduction rule takes our proof of P and our proof of Q
to spit out our proof of P ∧ Q.-/

-- #7
example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) :=
-- "if P and (Q or R), then (P and Q) or (P and R)"
-- "if (P and Q) or (P and R), then P and (Q or R)"
begin
  assume P Q R,
  apply iff.intro _ _,
  -- forward
  assume pqr,
  have p : P := and.elim_left pqr,
  have qr : Q ∨ R := and.elim_right pqr,
  apply or.elim qr, -- creates 2 goals (case analysis)
  assume q,
  apply or.intro_left (P ∧ R) (and.intro p q),
  assume r,
  apply or.intro_right (P ∧ Q) (and.intro p r),
  -- backward
  assume pandq_or_pandr,
  apply and.intro _ _,
  apply or.elim pandq_or_pandr, -- before: goals were to provide a proof of P and a proof of Q ∨ R; now: get a proof of p from the sub-and props.
  -- assume the left side of the first sub-and prop (which is P ∧ Q)
  assume pandq,
  apply and.elim_left pandq,
  -- assume the left side of the second sub-and prop (which is P ∧ R)
  assume pandr,
  apply and.elim_left pandr,
  -- 1 goal left: prove Q ∨ R
  apply or.elim pandq_or_pandr,
  assume pandq, -- to get proof of Q
  apply or.intro_left R (and.elim_right pandq), -- q (proof of Q) is in the parentheses
  assume pandr, -- to get proof of R
  apply or.intro_right Q (and.elim_right pandr),
end
/-
Paste.

P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R) by the use of the "implies"
introduction rule, which assumes our premise is true. Given
this proof, we may have an additional proof of P, which is
obtained by using the left "and" elimination rule, and a
a proof of Q ∨ R, which is obtained by using the right "and"
elimination rule. We further divide up our original
proposition by using the "or" elimination rule on the proof
of Q ∨ R. With this, we may perform case analysis. First,
we assume Q and obtain a proof of the conclusion with the
proposition P ∧ R and our constructed proof of P ∧ Q (left
"or" intro rule). Then, we assume R and use the right "or"
intro rule to obtain a proof of the conclusion in this case
with the proposition P ∧ Q and our constructed "and" proof
of P ∧ R. Like with P ∧ Q, we used the "and" introduction
rule.

(P ∧ Q) ∨ (P ∧ R) → P ∧ (Q ∨ R) with the assumption that
(P ∧ Q) ∨ (P ∧ R) is true. We want to prove an "and"
proposition, so we use the "and" introduction rule, which
needs proofs of its side propositions. We use the "or"
elimination rule to perform case analysis for its sides.
The left side, we assume as true and apply the left "and"
elimination rule to retrieve a proof of P. Then, we assume
P ∧ R is true and apply the left "and" elimination rule to
it to get a proof of P. The remaining side to prove is
Q ∨ R, so we apply the "or" elimination rule to do case
analysis. We assume P ∧ Q and prove the larger "or"
proposition by applying the left "or" intro rule on our
proof of q which was obtained by applying the right "and"
elimination rule on P ∧ Q. Finally, we assume P ∧ R is true,
this proof is applied with the right "or" intro rule with
the proposition Q and a proof of R through the right "and"
elimination rule on P ∧ R.
-/

-- #8
example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) :=
begin
  assume P Q R,
  apply iff.intro _ _,
  -- forwards
  assume p_or_qandr,
  apply or.elim p_or_qandr,
  assume p,
  apply and.intro _ _,
  ---- Goal: Prove P ∨ Q.
  apply or.intro_left Q p,
  ---- Goal: Prove P ∨ R.
  apply or.intro_left R p,
  assume qandr,
  apply and.intro _ _,
  ---- Goal: Prove P ∨ Q. (w/ a proof of Q)
  apply or.intro_right P (and.elim_left qandr),
  ---- Goal: Prove P ∨ R. (w/ a proof of R)
  apply or.intro_right P (and.elim_right qandr),
  -- backwards
  assume porq_and_porr,
  have porq : P ∨ Q := and.elim_left porq_and_porr,
  have porr : P ∨ R := and.elim_right porq_and_porr,
  apply or.elim porq,
  assume p,
  apply or.intro_left (Q ∧ R) p,
  assume q,
  apply or.elim porr, --!
  assume p,
  apply or.intro_left (Q ∧ R) p,
  assume r,
  apply or.intro_right P (and.intro q r),
end
/-
Paste.

P ∨ (Q ∧ R) → (P ∨ Q) ∧ (P ∨ R) by first assuming that our
premise is true. Then, apply the "or" elimination rule to
perform case analysis. In the first case, we must assume P,
with which we use the context to prove our conclusion. We
do this by using the "and" introduction rule. The first proof
that we need for this rule is obtained by using the left "or"
introduction rule with the proposition Q and the proof of P.
The second proof is obtained by using the left "or"
introduction rule with the proposition R and the proof of P.
With this side done, we then assume Q ∧ R. We also need the
"and" introduction rule for this, so we obtain the necessary
proofs with the right "or" introduction rule on proposition P
and a proof of Q (from the left "and" elimination rule)
-/

-- #9
example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P :=
begin
  assume P Q,
  apply iff.intro _ _,
  -- forwards
  assume p_and_porq,
  exact and.elim_left p_and_porq,
  -- backwards
  assume p,
  apply and.intro p _,
  apply or.intro_left Q p,
end

-- #10
example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P :=
begin
  assume P Q,
  apply iff.intro _ _,
  -- forwards
  assume p_or_pandq,
  apply or.elim p_or_pandq,
  assume p,
  apply p,
  assume pandq,
  apply and.elim_left pandq,
  -- backwards
  assume p,
  apply or.intro_left (P ∧ Q) p,
end

-- #11
example : ∀ (P : Prop), P ∨ true ↔ true :=
begin
  assume P,
  apply iff.intro _ _,
  -- forwards
  assume portrue,
  /-
  apply or.elim portrue,
  assume p,
  apply or.intro_left true p,
  -/
  apply true.intro,
  -- backwards
  assume t,
  apply or.intro_right P t,
end

-- #12
example : ∀ (P : Prop), P ∨ false ↔ P :=
begin
  assume P,
  apply iff.intro _ _,
  -- forward
  assume p_or_false,
  -- do case analysis?
  apply or.elim p_or_false,
  --- P → P
  assume p,
  exact p,
  --- false → P
  assume f,
end

-- #13
example : ∀ (P : Prop), P ∧ true ↔ P :=
begin
  assume P,
  apply iff.intro _ _,
  -- forwards
  assume p_and_true,
  apply and.elim_left p_and_true,
  -- backwards
  assume p,
  apply and.intro p true.intro,
end

-- #14
example : ∀ (P : Prop), P ∧ false ↔ false :=
begin
  assume P,
  apply iff.intro _ _,
  -- forwards
  assume p_and_false,
  apply and.elim_right p_and_false,
  -- backwards
  assume f,
  apply and.intro _ f,
  assume p,
end