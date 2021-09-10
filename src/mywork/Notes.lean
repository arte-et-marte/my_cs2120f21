/-
Axiom:

Equality is reflexive.

=> "Everything is equal to itself."

=> "t = t, given some type, T, and some object, t, of that type."

=>
-/
axiom eq_is_refl :
  ∀ (T : Type) (t : T),
  t = t
/-
=> eq.refl
-/


/-
Axiom:

Equals may be substituted for each other.

=> "Given some type, T, of objects, some property, P, of objects of that type, the knowledge that x has property P, and the knowledge that x = y, y has property P."

=>
-/
axiom eqls_are_swap :
  ∀ (T : Type) (P : T → Prop) (x y : T) (p1 : x = y) (p2 : P x),
  P y
/-
=> eq.subst
-/

/- --------------------- -/

/-
Conjecture:

Equality is symmetric.

-/
def eq_is_symm : Prop :=
  ∀ (T : Type) (x y : T),
  x = y → y = x


/-
Conjecture:

Equality is transitive.

-/
def eq_is_trans : Prop :=
  ∀ (T : Type) (x y z : T),
  x = y → y = z → x = z

/- --------------------- -/

/-
Proof:

(for eq_is_symm)
-/
example : eq_is_symm :=
begin
  unfold eq_is_symm,
  assume T x y p,
  rw p
end

/-alternatively,-/
example : eq_is_symm :=
begin
  unfold eq_is_symm,
  assume T x y p,
  apply eq.subst p,
  exact eq.refl x /-or, apply eq.refl x-/
end


/-
Proof:

(for eq_is_trans)
-/
example : eq_is_trans :=
begin
  unfold eq_is_trans,
  assume T x y z p1 p2,
  rw p1,
  exact p2
end

/-alternatively,-/
example : eq_is_trans :=
begin
  unfold eq_is_trans,
  assume T x y z p1 p2,
  rw p1,
  rw p2
end

/- --------------------- -/

/-
Theorems:
- eq.symm
- eq.trans
-/

/- --------------------- -/

/-
Practice (proving propositions):

-/
example : ∀ (T : Type) (x y z : T), x = y → y = z → z = x :=
begin
  assume T x y z p1 p2,
  apply eq.symm _,
  apply eq.trans p1 p2
end

/-alternatively,-/
theorem z_equals_x:
  ∀ (T : Type) (x y z : T) (p1 : x = y) (p2 : y = z), z = x :=
  begin
    assume (T : Type),
    assume (x y z : T),
    assume (p1 : x = y),
    assume (p2 : y = z),
    rw p1,
    rw p2
  end

/-
9.8.2021 Notes:

Intro rule (helps to build a proof) in Python - returns thing of given type, elim rule
(helps to use a proof (e.g., by re-writing it)) in Python - takes that thing as an arg. =: intro rule (eq.refl), elim
rule (eq.subst), what is the intro rule for different logical connectives? (See lecture 4 file).

lect 5

AND (logical connective):
(P Q : Prop)
P ∧ Q (P and Q)
when is this prop true? When p is true and q is true. Need two proofs, for each prop. Pair of proofs is the proof for
the bigger prop.
Lean: and.intro - func that takes an arg of type P, takes an arg of type Q, returns a proof of P ∧ Q.
(an intro rule bc it returns a proof)
and has two elim rules, one for left proof, one for right proof.
-/

/-
9.10.2021 Notes:
GitHub ID, statement: confidence lvl
-/