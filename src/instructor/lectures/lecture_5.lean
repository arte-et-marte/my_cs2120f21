/-
INTRODUCTION and ELIMINATION RULES
-/

/-
For ∀ x, P x (every x has property P)
  - introduction rule: assume arbitrary x, then show P x
  - elimination rule: *apply* a proof of ∀ x, P x, as a 
  kind of function to a specific value of x, say k, to 
  produce a proof of P k.
-/

theorem silly : ∀ (n : ℕ), true :=
begin
  assume (n : ℕ),
  exact true.intro, 
end

/-
My Notes:
"true" proposition is just always true.
goal translated: if you give me a value of type nat, I'll give you a proof that true is true.
trying to prove an implication. How do we prove an implication? Assume...return proof.
-/

/-
The proposition true is unconditionally true,
as proven by an always available proof called
(in Lean) true.intro.
-/

#check silly 7 /-applying to the number 7, elim rule: apply to args, return some result.-/

/-
The check command will tell you the type of any
expression (aka term) in Lean. Here we can see 
that silly is like a function, and that when we
apply it to the specific argument, 7, we get back
a proof of the resulting proposition (which is 
just, "true"). We'll soon be equipped to deal
with more interesting "return types".
-/

/-
For P → Q (if P is true then Q must also be true)
- introduction rule: assume arbitrary P, then show Q
- elimination rule: *apply* a proof of P → Q, as a
kind of function, to any proof of P to derive a proof of Q!
-/

theorem foo : ∀ (x : ℕ), x = 0 → x + 1 = 1 := 
begin
  assume x h,
  rw h,
end


/-
My Notes:
for all, apply intro rule for for all, assume given value of nat,
assume given proof (that x = 0), in that context show that x+1=1.
what do you have in context that - have x=0, how to use? use it to rw
x as 0 in our goal, get 0 + 1 = 1, which eq.refl will take care of. use
rw when there is something in the context to change for the goal.-/
/-
Wow! ∀ and → sure do seem similar. Indeed they're the same!
They define function types. We construct a proof of ∀ or → 
by assuming the premise and showing that in that context we
can derive a result of the conclusion type. We can then use
a proof of a ∀ or → by treating it as a function that can
be applied to a specific value to derive a proof *for that
specific value. Indeed, in Lean, → is really just another
notation for forall!
-/

/-
Intro rule for ∧

Give a proof of P and a proof of Q get back a proof of (P ∧ Q)
-/

axioms (P Q : Prop)

#check P
#check (P ∧ Q)

axioms (p : P) /-assume proof of P-/ (q : Q)
example : P ∧ Q := and.intro p q /-trying to prove that P ∧ Q, apply
and's intro rule, which needs a proof of P and a proof of Q.-/

/-Prove that if arbitrary props. P and Q are true (which is to say that
we have a proof of each of them), that the prop of P ∧ Q is also true. 

Proof: The conjecture that P ∧ Q is true is proved by application of 
the introduction rule for and. (which returns a pair of proofs for the
larger proof?)-/

example : 0 = 0 ∧ 1 = 1 :=
begin
  apply and.intro _ _, /-1st slot: proof of 0=0 (P), 2nd slot: proof of 1=1 (Q)-/
  apply eq.refl 0, /-gives a proof of 0 = 0-/
  apply eq.refl 1 /-gives a proof to 1 = 1, to accomplish goal-/
end
/-we assume only if we have premises to our proposition-/

example : 0 = 0 ∧ 1 = 1 :=
begin
  apply and.intro (eq.refl 0) (eq.refl 1)
end

theorem bar : 0 = 0 ∧ 1 = 1 :=
begin
  apply and.intro (eq.refl 0) (eq.refl 1),
end

#check bar
#check and.elim_left bar
#check and.elim_right bar

theorem and_commutative : ∀ (P Q : Prop), P ∧ Q → Q ∧ P :=
begin
    assume P Q h,
    apply and.intro _ _, /-proof of p and proof q individually-/
    apply and.elim_right h, /-gives back q from p ∧ q-/
    apply and.elim_left h, /-gives us p from h-/
end
