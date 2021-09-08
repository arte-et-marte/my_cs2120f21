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