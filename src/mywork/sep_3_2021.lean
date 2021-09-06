/-
Theorem: Equality is symmetric.

Note(s): assume the premises of the conjecture are true, to prove that something is true for all objects of a any type
pick an arbitrary object of an arbitrary type, if we want to prove an implication (if-then) assume that we have a proof
of that statement, equality relation an enabler of the use of the substitutability axiom, theorem keyword signals the
creation of a proof, theorem keyword could be replaced with def keyword.
-/

theorem eq_is_symm :
  ∀ (T : Type) (x y : T), x = y → y = x :=
  begin
    assume (T : Type),
    assume (x y : T),
    assume (e : x = y), /-assuming that we have a proof of our implication-/
    rw e
  end

/-
Theorem: ∀ (T : Type) (x y : T), x = y → y = x.
Proof: Assume that T is any type and that we have objects of x and y of this type. Remaining to be shown is that if x = y
, then y = x. To prove this, we'll assume the premise that x = y. We need to prove y = x. By the axiom of the substitutability
of equals, and the assumed fact that x = y, we can REWRITE the x in the goal as y, yielding y = y as our new proof goal.
This is true by the axiom of the reflexivity of equality. QED (quod est demonstratum - thus it is shown).
-/

/-
Theorem: Equality is transitive.

Note(s): assume T is shorthand. substitutability takes an argument a proof of equality.
-/

theorem eq_is_trans :
  ∀ (T : Type) (x y z : T), x = y → y = z → x = z :=
begin
  assume T,
  assume x y z,
  assume e1,
  assume e2,
  rw e1,
  exact e2
end

/-x=y, y=z, prove z=x-/

theorem z_equals_x :
  ∀ (T : Type) (x y z : T), x = y → y = z → x = z → z = x :=
begin
  assume (T : Type),
  assume (x y z : T),
  assume (e1 : x = y),
  assume (e2 : y = z),
  assume (e3 : x = z),
  
end