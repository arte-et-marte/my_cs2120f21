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

/-
9.13.2021 Notes
#1 - How do I write a conditional?
axiom keyword (sg.), axioms (pl.) - props. that assume true.
-/
namespace implies
axioms (P Q : Prop)
def if_P_is_true_then_so_is_Q : Prop := P → Q
-- assume P is true
axiom p : P
-- assume we have a proof of P (p)

axiom pq : P → Q
-- = axiom pq : if_P_is_true_then_so_is_Q
-- assume that we have a proof of P → Q

/-
implies rules:
→ intro rule 
assume premise (is true), show conclusion 
→ elim rule
apply implies relationship (proof of relationship, pq, for example) to premise
-/


#check p
#check pq
#check (pq p) /- → elim rule on p-/
end implies

/-Suppose that P and Q are propositions and you know that P → Q and that P are both true. Show that Q is true.begin

Proof: Apply the truth of P →Q to the truth of P to derive the truth of Q. / By the elimination rule for → with pq applied
to p.-/

/-
∀ Rules:
-/
namespace all
axioms (T : Type) (pOfT : T → Prop ) (t : T) (a : ∀ (x : T), pOfT x)

-- Does t have property P? Yes, bc it is of Type T (∀ move from general statement about every object of a kind to a statement about a specific object of that kind)
end all

-- elim rule: assume a forall statement about a type of objects is true and assume that you have an object of that type, apply that statement to that object to prove that that object has the property of that type.
-- takes an object of a type, returns a proof for that object having that type's property

/-
-/
axioms (P Q : Prop)
/-
Want a proof of P ∧ Q.-/

/-Implies: IF P is true, THEN, Q is true.
  And: P is true and Q is also true. (an ordered pair of proofs)-/
/-
#2 - Elimination rules.

#3 - Rules for ∀ vs →.

#4 - have in Lean.

#5 - 
-/