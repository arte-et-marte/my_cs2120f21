/- 
   *******************************
   PART 1 of 2: AXIOMS [50 points]
   *******************************
-/

/-
Explain the inference (introduction and
elimination) rules of predicate logic as
directed below. To give you guidance on
how to answer these questions we include
answers for some questions.
-/


-- -------------------------------------

/- #1: → implies [5 points]

INTRODUCTION

Explain the introduction rule for →. 

[We give you the answer here.]

In English: Given propositions, P and Q, 
a derivation (computation) a proof of Q 
from any proof of P, is a proof of P → Q.

In constructive logic, a derivation is a
given as a function definition. A proof
of P → Q literally is a function, that,
when given any proof of P as an argument
returns a proof of Q. If you define such
a function, you have proved P → Q.

ELIMINATION

Complete the definition of the elimination
rule for →.

(P Q : Prop) (p2q : P → Q) (p : P)
----------------------------------
     (q : Q) -- **Ans.**
-/

-- Give a formal proof of the following
example : ∀ (P Q : Prop) (p2q : P → Q) (p : P), Q :=
begin
  assume P Q p2q p, -- **Ans.**
  have q : Q := p2q p,
  exact q,
end

-- Extra credit [2 points]. Who invented this principle?



-- -------------------------------------

/- #2: true [5 points]

INTRODUCTION

Give the introduction rule for true using
inference rule notation.

[Here's our answer.]

---------- intro
(pf: true)

Give a brief English language explanation of
the introduction rule for true.

-- The introduction rule for true provides -- **Ans.**
that a proof of true is constructed by simply
accepting that true is true.

ELIMINATION

Give an English language description of the
eliimination rule for true.

[Our answer]

A proof of true carries no information so
there's no use for an elimination rule.
-/

-- Give a formal proof of the following:

example : true := true.intro -- **Ans.**

-- -------------------------------------

/- #3: ∧ - and [10 points]

INTRODUCTION

Using inference rule notation, give the 
introduction rule for ∧.

[Our answer]

(P Q : Prop) (p : P) (q : Q)
---------------------------- intro
        (pq : P ∧ Q)

Given an English language description of
this inference rule. What does it really
say, in plain simple English. 

The and introduction rule provides that **Ans.**
a proof of an and proposition is
constructed by providing a proof of the
left proposition and a proof of the right
proposition. In other words, if you were
to prove the proposition that "My cat is
cute and fluffy," then you would need to
assume that "My cat is cute" and "My cat
is fluffy" are propositions and have a proof
of each of these propositions.

ELIMINATION

Give the elimination rules for ∧ in both
inference rule and English language forms.

Inference rule notation: **Ans.**
(P Q : Prop) (p_and_q : P ∧ Q)
------------------------------ (and.elim_left)
            (p : P)

(P Q : Prop) (p_and_q : P ∧ Q)
------------------------------ (and.elim_right)
            (q : Q)

English description: **Ans.**
The left and elimination rule provides that a
proof of the left proposition is obtained when
there is a proof of the left proposition AND
a proof of the right proposition, that is, when
there is a proof of the and proposition. The
right introduction rule provides the same thing
except for the right proposition. In other
words, if you were to have a proof of the
proposition that "I have a million dollars and
it is sunny in Honolulu today", then you would know
for a fact that I have a million dollars (left
and elimination rule) and that it is sunny in
Honolulu today (right introduction rule).
-/

/-
Formally state and prove the theorem that, 
for any propositions P and Q,  Q ∧ P → P. 
-/

example : ∀ (P Q : Prop), Q ∧ P → P := -- **Ans.**
begin
  assume P Q q_and_p,
  have p : P := and.elim_right q_and_p,
  exact p,
end

-- -------------------------------------

/- #4: ∀ - for all [10 points]

INTRODUCTION

Explain in English the introduction rule for ∀. If 
T is any type (such as nat) and Q is any proposition 
(often in the form of a predicate on values of the
given type), how do you prove ∀ (t : T), Q? What is
the introduction rule for ∀?

-- The introduction rule for ∀ provides that a proof -- **Ans.**
of something (e.g., Q) given an arbitrary something
of a certain type may be constructed by simply assuming
that we have some arbitrary something of that type
and showing that that something makes Q true. By showing
that that arbitrarily selected something of the
specified type can prove Q, the proposition ∀ (t : T),
Q is thus proven.

ELIMINATION

Here's an inference rule representation of the elim
rule for ∀. First, complete the inference rule by
filling in the bottom half, then Explain in English
what it says.

(T : Type) (Q : Prop), (pf : ∀ (t : T), Q) (t : T)
-------------------------------------------------- elim
                (q : Q) **Ans.**

-- You can obtain a proof of Q provided that you have **Ans.**
a specified type, T, a proposition about something of
that type, Q, a proof of the proposition that Q is true
for all things of that type, and a proof that you have
something of that type, t. This is what the elimination
rule for ∀ provides.

Given a proof, (pf : ∀ (t : T), Q), and a value, (t : T),
briefly explain in English how you *use* pf to derive a
proof of Q.

-- I would provide pf t. That is, I would apply pf to t. **Ans.**
-/

/-
Consider the following assumptions, and then in the
context of these assumptions, given answers to the
challenge problems.
-/

axioms
  (Person : Type)
  (KnowsLogic BetterComputerScientist : Person → Prop) -- Given a person, the propositions KnowsLogic and BetterComputerScientist will be returned.
  (LogicMakesYouBetterAtCS: 
    ∀ (p : Person), KnowsLogic p → BetterComputerScientist p)
  -- formalize the following assumptions here
  -- (1) Lynn is a person
  (Lynn : Person) --**Ans.**
  -- (2) Lynn knows logic
  (LynnKnowsLogic : KnowsLogic Lynn) -- **Ans.**
  -- add answer here
  -- add answer here

/-
Now, formally state and prove the proposition that
Lynn is a better computer scientist
-/
example : BetterComputerScientist Lynn := -- **Ans.**
begin
  apply LogicMakesYouBetterAtCS Lynn LynnKnowsLogic,
end

-- -------------------------------------

/- #5: ¬ - not [10 points] 

The ¬ connective in Lean is short for *not*. Give
the short formal definition of ¬ in Lean. Note that
surround the place where you give your answer with
a namespace. This is just to avoid conflicting with
Lean's definition of not.
-/

namespace hidden
def not (P : Prop) := P → false  -- fill in the placeholder -- **Ans.**
end hidden

/-
Explain precisely in English the "proof strategy"
of "proof by negation." Explain how one uses this
strategy to prove a proposition, ¬P. 
-/

-- We use the proof by negation when we want to **Ans.**
-- prove that P → ¬P. In other words, we want to
-- show that from a proof of P, we can say that
-- there is no proof of P. The only way that this
-- proposition can be true is if we show that a
-- proof of P leads to a contradiction. From this
-- contradiction, anything may follow, and thus,
-- we can prove that P → ¬P.

/-
Explain precisely in English the "proof strategy"
of "proof by contradiction." Explain how one uses
this strategy to prove a proposition, P (notice 
the lack of a ¬ in front of the P). 

Fill in the blanks the following partial answer:

To prove P, assume __¬P__ and show that __a contradiction follows__. **Ans.**
From this derivation you can conclude __¬¬P__.
Then you apply the rule of negation __elimination__
to that result to arrive at a proof of P. We have
seen that the inference rule you apply in the 
last step is not constructively valid but that it
is __classically__ valid, and that accepting the axiom
of the __excluded middle__ suffices to establish negation
__elimination__ (better called double __false__ __elimination__)
as a theorem.
-/

-- -------------------------------------

/- 
#6: ↔ - if and only if, equivalent to [10 points]
-/

/-
ELIMINATION 

As with ∧, ↔ has two elimination rules. You can 
see their statements here.
-/
#check @iff.elim_left
#check @iff.elim_right

/-
Formally state and prove the theorem that 
biimplication, ↔, is *commutative*. Note: 
put parentheses around each ↔ proposition,
as → has higher precedence than ↔. Recall
that iff has both elim_left and elim_right
rules, just like ∧.
-/

example : ∀ (P Q : Prop), (P ↔ Q) → (Q ↔ P) := -- **Ans.**
begin
  assume P Q p_iff_q,
  have p_iff_q_left : P → Q := iff.elim_left p_iff_q,
  have p_iff_q_right : Q → P := iff.elim_right p_iff_q,
  exact iff.intro p_iff_q_right p_iff_q_left,
end

/- 
   ************************************************
   PART 2 of 3: PROPOSITIONS AND PROOFS [50 points]
   ************************************************
-/

/- #7 [20 points]

First, give a fluent English rendition of
the following proposition. Note that the
identifier we use, elantp, is short for
"everyone likes a nice, talented person."
Then give a formal proof. Hint: try the
"intros" tactic by itself where you'd
previously have used assume followed by
a list of identifiers. Think about what
each expression means. 
-/

def ELJL : Prop := 
  ∀ (Person : Type) 
    (Nice : Person → Prop)
    (Talented : Person → Prop)
    (Likes : Person → Person → Prop)
    (elantp : ∀ (p : Person), 
      Nice p → Talented p → 
      ∀ (q : Person), Likes q p)
    (JohnLennon : Person)
    (JLNT : Nice JohnLennon ∧ Talented JohnLennon),
    (∀ (p : Person), Likes p JohnLennon) 
    
/-
For all things of type Person, Nice, Talented, and Likes are propositions **Ans.**
that may be made about them. Provided also is a proof that for all p of
type Person, if p is Nice and p is Talented, then for all q of type Person,
q likes p. JohnLennon is a Person, and he is both Nice and Talented. Thus,
for all p of type Person, p must like JohnLennon.
-/

example : ELJL := -- **Ans.**
begin
  assume Person,
  assume Nice Talented,
  assume Likes,
  assume everyone_likes_a_nice_and_talented_person,
  assume JohnLennon,
  assume john_lennon_is_nice_and_talented,
  assume p,
  apply everyone_likes_a_nice_and_talented_person,
  exact and.elim_left john_lennon_is_nice_and_talented,
  exact and.elim_right john_lennon_is_nice_and_talented,
end



/- #8 [10 points]

If every car is either heavy or light, and red or 
blue, and we want a prove by cases that every car 
is rad, then: 

-- how many cases will need to be considered? 3 **Ans.**
-- list the cases (informaly)
    -- Heavy car that is red,
    -- Heavy car that is blue,
    -- Light car that is red or blue

-/

/-
  *********
  RELATIONS
  *********
-/


/- #9 [20 points]
Equality can be understood as a binary relation
on objects of a given type. There is a binary 
equality relation on natural numbers, rational 
numbers, on strings, on Booleans, and so forth.

We also saw that from the two axioms (inference
rules) for equality, we could prove that it is
not only reflexive, but also both symmetric and
transitive.

Complete the following definitions to express
the propositions that equality is respectively
symmetric and transitive. (Don't worry about
proving these propositions. We just want you
to write them formally, to show that you what
the terms means.)
-/

def equality_is_symmetric : Prop := ∀ (T : Type) (x y : T), x = y → y = x -- **Ans.**
def equality_is_transitive : Prop := ∀ (T : Type) (x y z : T), x = y → y = z → x = z

/-
  ************
  EXTRA CREDIT
  ************
-/

/- 
EXTRA CREDIT: State and prove the proposition
that (double) negation elimination is equivalent
to excluded middle. You get 1 point for writing
the correct proposition, 2 points for proving it
in one direction and five points for proving it
both directions. 
-/

def negelim_equiv_exmid : Prop := 
  ∀ (P : Prop),
  ¬¬P → P ↔ P ∨ ¬P

example : negelim_equiv_exmid :=
begin
  assume P,
  apply iff.intro _ _,
  -- forwards
  assume nnp_imp_p,
  have p_or_np := classical.em P,
  cases p_or_np with p np,
  exact or.intro_left (¬P) p,
  exact or.intro_right (P) np,
  -- backwards
  assume p_or_np,
  assume nnp,
  cases p_or_np with p np,
  assumption,
  contradiction,
end

/- 
EXTRA CREDIT: Formally express and prove the
proposition that if there is someone everyone
loves, and loves is a symmetric relation, then 
thre is someone who loves everyone. [5 points]
-/

axiom Loves : Person → Person → Prop

example : (∃ (p : Person), ∀ (q : Person), Loves q p) → (∃ (p : Person), ∀ (q : Person), Loves p q) :=
begin
  assume l,
  have r_or_nr := classical.em (∃ (p : Person), ∀ (q : Person), Loves p q),
  cases r_or_nr with r nr,
  assumption,
  -- contradiction somewhere
end
