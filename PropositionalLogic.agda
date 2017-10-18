module PropositionalLogic where

{-
We shall now show the correspondence between propositions and sets for propositional logic. This correspondence was discovered by Curry, who noticed that there is a correspondence between some basic combinators in the lambda calculus and some axioms for implication.

For example, the type of the identity combinator 
-}

I : {A : Set} → A → A
I x = x

{-
corresponds to the axiom A ⊃ A, where ⊃ is implication. The type of the composition combinator corresponds
-}

B : {A B C : Set} → (B → C) → (A → B) → A → C
B g f x = g (f x)

{-
axiom  (B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C. Similarly the type of the constant combinator 
-}

K : {A B : Set} → A → B → A
K x y = x

{-
corresponds to the axiom A ⊃ B ⊃ A. And finally, the type of
-}

S : {A B C : Set} → (A → B → C) → (A → B) → A → C
S g f x = g x (f x)

{-
corresponds to the axiom (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C.

Finally modus ponens (the rule that says that from A ⊃ B and A deduce B) corresponds to the typing rule for application (from f : A ⊃ B and a : A deduce f a : B). 

The intuitive idea is that a (constructive) proof f of an implication A ⊃ B is a function which maps proofs of A to proofs of B. In constructive (and intuitionistic) mathematics functions are computable, that is, they are "programs".

Furthermore, conjunction corresponds to Cartesian product
The type of the constructor corresponds to the "introduction rule" for conjunction:
-}

data _&_ (A B : Set) : Set where
  <_,_> : A → B → A & B

_∧_ : (A B : Set) → Set
_∧_ = _&_

_×_ : (A B : Set) → Set
_×_ = _&_

{-
Moreover, the projections correspond to "elimination rules"
-}

fst : {A B : Set} → A & B → A
fst < x , y > = x

snd : {A B : Set} → A & B → B
snd < x , y > = y

{-
Similarly disjoint union (sum) corresponds to disjunction and the types of the constructors correspond to introduction rules for disjunction:
-}

data _∨_ (A B : Set) : Set where
  inl : A → A ∨ B
  inr : B → A ∨ B

infixr 0 _∨_

{-
Moreover, definition by cases corresponds to proof by cases (the disjunction elimination rule):
-}

case : {A B C : Set} → (A → C) → (B → C) → A ∨ B → C
case f g (inl x) =  f x
case f g (inr y) =  g y

{-
Let us now construct a simple proof, the proof of commutativity of conjunction:
-}

comm-∨ : {A B : Set} → A ∨ B → B ∨ A 
comm-∨ (inl a) = inr a
comm-∨ (inr b) = inl b

{-
Exercise: Prove commutativity of conjunction!

Finally, we point out that the the unit set corresponds to a trivially true proposition:
-}

data ⊤ : Set where
  <> : ⊤

{-
Similarly, the empty set is defined as the set with no constructors and corresponds to a trivially false proposition:
-}

data ⊥ : Set where

{-
The elimination rule for ⊥ (it implies anything) corresponds to the rule of proof by no case. If we pattern match on the constructors for ⊥ we get no cases. However, rather than simply not writing out any cases at all, Agda writes one line
-}

nocase : {C : Set} → ⊥ → C
nocase ()

{-
where () indicates the argument which cannot be instantiated in a type-correct way.

Note that there is a general pattern for all the logical connectives, except ⊃, stating that the types of the constructors correspond to the introduction rules. If we want to have this pattern for ⊃ as well, we can alternatively define it as follows:
-}

data _⊃_ (A B : Set) : Set where
  ⊃-intro : (A → B) → A ⊃ B

{-
Modus ponens is now defined as follows
-}

mp : {A B : Set} → A ⊃ B → A → B
mp (⊃-intro g) a = g a

{- 
Negation is defined as implying the absurd:
-}

¬_ : Set → Set
¬_ A = A → ⊥

{-
With this definition neither excluded middle

em : (A : Set) → A ∨ ¬ A
em A = {!!}

nor double negation

dn :  (A : Set) → ¬ (¬ A) → A
dn A g = {!!}

are valid.

However, the inverse of double negation is valid:
-}

inverse-dn : (A : Set) → A → ¬ (¬ A)
inverse-dn A a = λ f → f a

{-
This is called the BHK (Brouwer-Heyting-Kolmogorov) interpretation of logic or the Curry-Howard correspondence between propositions as types (sets). Howard showed how to generalize this to predicate logic by introducing dependent types.

Exercise: Prove the following three laws. 
(a) the law of triple negation:

tn :  (A : Set) → ¬ (¬ (¬ A)) → ¬ A

(b) excluded middle implies double negation:

em-dn : {A : Set} → (A ∨ ¬ A) →  ¬ (¬ A) → A

(c) double negation implies excluded middle:

dn-em : ({X : Set} → ¬ (¬ X) → X) → (A : Set) →  (A ∨ ¬ A)

Note the strengthening of the assumption here: to prove excluded middle for A it does not suffice to know double negation for A only but you assume you know it for any proposition X.
-}
