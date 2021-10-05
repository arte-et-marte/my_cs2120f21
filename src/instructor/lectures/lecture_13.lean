/-
UPDATE: Test distributed after class on 
Monday. Monday will be a review day. The
test is due back Wednesday before class.
In class Wednesday we will have at least
a short quiz to sanity check what you will
have submitted for the test. We reserve the
right to do follow-on in-person testing if
the results indicate a possible problem.
-/

/-
REVIEW: Last time we focused on the question, 
how do we construct a proof of ∃ x, P x.  

-- there exists an x that satisfies P, pick value
-- for x and show that x that has the property

To do so, you apply the introduction rule for
exists. It's called exists.intro in Lean. You
apply it to two arguments: a specific value, w,
in place of x, and a proof that that particular
w satisfies the predicate, P, i.e., that there 
is a proof of the proposition, P w. 

-- w was natural #s, eq proofs (lect 11)

In other words, you can think of a proof of
∃ x, P x, as a pair, ⟨w, pf ⟩, where w is a
witness and pf is a proof of P w.
-/

/-
Today we'll delve deeper into the mysteries
of exists elimination, or how you can *use*
a proof of ∃ x, P x.

Here's the idea: If you have a proof, ex, of
of ∃ (x : X), P x, you can apply exists.elim
to ex, and (after a few more simple maneuvers)
have yourself a specific value, (w : X), and 
a proof that w satisfies P, i.e., (pf : P w). -- from a proof ex, get w and pf back
The idea is that you can then uses the values
in your subsequent proof steps.

Why does this rule make sense? Consider a very
simple example. If I tell you there exists some
green ball, you can say, "well, call it b," and
give that we know it's green, we also know that
it satisfies the isGreen _ predicate, so we can
also assume we have a proof of (isGreen b). In
this example, b is a witness to the fact that
some object satisfies the predicate. The proof
then shows for sure that that is so.
-/

example : ∃ (b : bool), b && tt = ff :=
begin
  apply exists.intro ff _, -- plug witness value and a proof that it satisfies the predicate in question
  exact rfl, -- eq.refl applied to ff (ff == ff)
end

example :
  (∃ (b : bool), b && tt = ff) → (∃ (b : bool), true) := -- then, there exists a bool that satisfies the true predicate
begin
  assume h, -- existentially quantified proposition
  cases h with v pf,
  apply exists.intro v , -- v has the property we care about
  trivial, -- trivial knows true has a proof of itself
  /-
  assume h,
  cases h with w pf,
  apply exists.intro w,
  trivial,
  -/
  -- tt is the boolean, true is the proposition (true as a proposition - has a proof)
end

example : ∃ (b : bool), true :=
begin
  apply exists.intro ff _, -- tt or ff would work as w
  exact true.intro,
end

/-
Let's set up some assumptions so that 
we can explore their consequences when
it comes to existentially quantified
propositions.
-/

/-
Beachballs! What could be more fun
-/

axioms 
  (Ball : Type)           -- There are balls
  (Green : Ball → Prop)   -- a Ball can be Green
  (Red : Ball → Prop)     -- a Ball can be Red 
  (b1 b2 : Ball)          -- b1 and b2 are balls
  (b1r : Red b1)          -- b1 is red
  (b1g : Green b1)        -- b1 is green
  (b2r : Red b2)          -- b2 is red


example : 
  (∃ (b : Ball), Red b ∧ Green b) → 
  (∃ (b : Ball), Red b) :=
begin
  assume w,
  cases w with b h, -- applying exists.elim, 1st case: assume b of type ball, know that it's red and green
  -- cases applying exists.elim which takes a proof of an exists statement and spits out the witness value, predicate proof
  -- to prove exists statement, need exists intro rule
  apply exists.intro b (and.elim_left h),

  assume h,
  cases h with b rb_and_gb, -- applying the exists elimination rule, which returns the w and the proof that w satisfies the predicate
  apply exists.intro b _,
  exact and.elim_left rb_and_gb,
end 

example : 
  (∃ (b : Ball), Red b ∨ Green b) → 
  (∃ (b : Ball), Green b ∨ Red b) :=
begin
  assume h,
  cases h with w pf,
  apply exists.intro w _,
  apply or.elim pf,
  -- tbc
end 

example : 
  (∃ (b : Ball), Red b ∨ Green b) → 
  (∃ (b : Ball), Red b) :=
begin
  assume h,
  cases h with w pf,
  apply or.elim pf,
  -- 1
  assume h1,
  apply exists.intro w _,
  assumption,
  -- 2
  -- tbc
end 

example : 
    (∃ (b : Ball), Red b) → 
    (∃ (b : Ball), Red b ∨ Green b) := 
begin
  -- 
end 

/-
Social Networks
-/

axioms
  (Person : Type) -- a person is a type
  (Nice : Person → Prop) -- nice is a function from person to prop, given a person, that person is nice
  (Likes : Person → Person → Prop) -- a function that takes in 2 people, returns prop that first person likes second person

example : 
-- if there is a person that everyone likes, then each person there is someone that they like
  (∃ (p1 : Person), ∀ (p2 : Person), Likes p2 p1) → 
  (∀ (e : Person), ∃ (s : Person), Likes e s) :=
-- there exists a person that everybody likes
-- for every person there exists someone that they like
-- forwards is true, backwards is not
begin
  assume h, -- there exists a person such that...
  -- big exists proof, need elim to split it up into component parts
  cases h with person1 w,
  -- forall statement now, first step assume
  assume person2,
  -- need person1 (our witness that satisfies pred)
  apply exists.intro person1 _,
  -- do we see anything that provides a proof of Likes - w!
  apply w person2,

  assume h,
  assume e,
  cases h with p pf,
  apply exists.intro p _, -- !!! TEST QUESTION !!!
  exact pf e,
end

/-
Write formal expressions for each of the following
English language sentences.
-/

-- Everyone likes him or herself
∀ (p : Person), Likes p p
-- Someone doesn't like him or herself
(∃ p : Person), ¬(Likes p p) -- not takes in a proposition
¬(∀ (p : Person)), Likes p p
-- There is someone likes someone else
∃ (p1 p2 : Person), Likes p1 p2
-- No one likes anyone who dislikes them
¬ (∃ (p : Person) ), ¬(Likes )
-- Everyone likes anyone who is nice

-- No one likes anyone who is not nice
¬ (∃ (p : Person)), ∀ (p2 : Person), ¬ Nice p2 → Likes p p2,
-- there exists a person such that (,) for all people, NOT p does like not nice p2

/-
If everyone who's nice likes someone, then
there is someone whom everyone who is nice 
likes.
-/
((∀ p : Person), (∃ p2 : Person), Nice p → Likes p p2) → (∃ (p : Person), ∀ (p2 : Person), Nice p2 → Likes p2 p)

example : ¬(∀ (p : Person), Likes p p) ↔ (∃ (p : Person), ¬(Likes p p)) :=
begin
  apply iff.intro _ _,
  -- forwards implication proof
  assume left, -- have a proof of an exists statement, which we can use elim on
  apply exists.intro _ 
end

example : ¬(∀ (p : Person), Likes p p) → (∃ (p : Person), ¬(Likes p p)) :=
begin
  assume h,
  have f := classical.em ((∃ (p : Person), ¬(Likes p p))),
  cases f,
  -- case 1
  assumption,
  -- want to prove a contradiction, which to build? build h's? how?
  have contra : ∀ (p : Person), Likes p p := _, -- set goal
  contradiction,
  -- case 2
  assume p,
  -- how to prove Likes p p
  have h := classical.em (Likes p p),
  cases h,
  -- subcase 1
  assumption,
  -- subcase 2
  have contra2 : ∃ (p : Person), ¬(Likes p p) := exists.intro p h,
  contradiction,
end

example : (∃ (p : Person), ¬(Likes p p)) → ¬(∀ (p : Person), Likes p p) :=
begin
  assume h,
  cases h with p pf,
  assume p2,
  have f := p2 p,
  contradiction,
end