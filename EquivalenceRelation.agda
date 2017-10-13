module EquivalenceClass where

open import Bool
open import Nat
open import NatProofs
open import Identity
open import PropositionalLogic
open import Product

postulate comm-plus : (n m : Nat) -> n + m ≡ m + n
postulate comm-mult : (n m : Nat) -> n * m ≡ m * n
postulate assoc-mult : (a b c : Nat) -> (a * b) * c ≡ a * (b * c)

{- equivalent relation for pairs of natural numbers -}

{-
a/b ~ c/d iff ad ≡ cb
-}

data _~_ : Nat × Nat -> Nat × Nat -> Set where
  rel : {a b c d : Nat} -> a * (d + 1) ≡ c * (b + 1) -> < a , b > ~ < c , d >

_/_ : (n m : Nat) -> Nat × Nat
n / m = < n , m >

refl~ : {p : Nat × Nat} -> p ~ p
refl~ {< _ , _ >} = rel refl

sym~ : {p q : Nat × Nat} -> p ~ q -> q ~ p
sym~ (rel x) = rel (sym x)

lemma-1 : (a b c d f : Nat) -> a * d ≡ c * b -> (a * d) * f ≡ (c * b) * f
lemma-1 a b c d f x = cong (λ y → y * f) x

lemma-2-1 : (c d e f : Nat) -> c * f ≡ e * d -> f * c ≡ e * d
lemma-2-1 c d e f x = trans (comm-mult f c) x

lemma-2-2 = lemma-1

lemma-2-3 : (b c d e f : Nat) -> (f * c) * b ≡ (e * d) * b -> f * (c * b) ≡ (e * d) * b
lemma-2-3 b c d e f x = trans (sym (assoc-mult f c b)) x

lemma-2-4 : (b c d e f : Nat) -> f * (c * b) ≡ (e * d) * b -> (c * b) * f ≡ (e * d) * b
lemma-2-4 b c d e f x = trans (comm-mult (c * b) f) x

lemma-2 : (b c d e f : Nat) -> c * f ≡ e * d -> (c * b) * f ≡ (e * d) * b
lemma-2 b c d e f x = lemma-2-4 b c d e f (lemma-2-3 b c d e f (lemma-1 f d e c b (lemma-2-1 c d e f x)))

lemma-3-1 : (a b c d e f : Nat) -> (a * d) * f ≡ (e * d) * b -> f * (a * d) ≡ b * (e * d)
lemma-3-1 a b c d e f x = trans (sym (comm-mult (a * d) f)) (trans x (comm-mult (e * d) b))

lemma-3-2 : (a b c d e f : Nat) -> f * (a * d) ≡ b * (e * d) -> (f * a) * d ≡ (b * e) * d
lemma-3-2 a b c d e f x = trans (assoc-mult f a d) (trans x (sym (assoc-mult b e d)))

lemma-3-3'' : (n m : Nat) -> succ n ≡ succ m -> n ≡ m
lemma-3-3'' n .n refl = refl

lemma-3-3' : (k n m : Nat) -> n + k ≡ m + k -> n ≡ m
lemma-3-3' zero n .n refl = refl
lemma-3-3' (succ k) n m x = lemma-3-3' k n m (lemma-3-3'' (n + k) (m + k) x)

lemma-⊥-2 : (m : Nat) -> 0 ≡ succ m -> ⊥
lemma-⊥-2 m ()

lemma-⊥-4 : (n m : Nat) -> 0 ≡ (succ m) * (succ n) -> ⊥
lemma-⊥-4 n m x = nocase (lemma-⊥-2 (succ m * n + m) (trans x (comm-plus (succ m) (succ m * n))))

lemma-3-3 : (n m d : Nat) -> (d + 1) * n ≡ (d + 1) * m -> n ≡ m
lemma-3-3 zero zero d refl = refl
lemma-3-3 zero (succ m) d x = nocase (lemma-⊥-4 m d x)
lemma-3-3 (succ n) zero d x = nocase (lemma-⊥-4 n d (sym x))
lemma-3-3 (succ n) (succ m) d x = cong succ (lemma-3-3 n m d (lemma-3-3' (d + 1) ((d + 1) * n) ((d + 1) * m) (trans (trans (comm-plus ((d + 1) * n) (d + 1)) x) (comm-plus ((d + 1)) ((d + 1) * m)))))

lemma-3-4 : (a b d e f : Nat) -> (f * a) * succ d ≡ (b * e) * succ d -> f * a ≡ b * e
lemma-3-4 a b d e f x = lemma-3-3 (f * a) (b * e) d (lemma-3-1 (f * a) (succ d) f (succ zero) (b * e) (succ d) x)

lemma-3-5 : (a b e f : Nat) -> f * a ≡ b * e -> a * f ≡ e * b
lemma-3-5 a b e f x = lemma-3-1 f e f (succ zero) b a x

lemma-3 : (a b c d e f : Nat) -> a * succ d ≡ c * b -> c * f ≡ e * succ d -> a * f ≡ e * b
lemma-3 a b c d e f x y = lemma-3-5 a b e f (lemma-3-4 a b d e f
                        (lemma-3-2 a b c (succ d) e f
                        (lemma-3-1 a b c (succ d) e f
                        (trans
                          (lemma-1 a b c (succ d) f x)
                          (lemma-2 b c (succ d) e f y)))))

trans~ : {p q r : Nat × Nat} -> p ~ q -> q ~ r -> p ~ r
trans~ {< a , b >} {< c , d >} {< e , f >} (rel x) (rel y) = rel (lemma-3 a (succ b) c d e (succ f) x y)


{- equivalent class for above equivalence relation, rational numbers -}

data Rat : Nat -> Nat -> Set where
  mkrat : {a b : Nat} -> (n m : Nat) -> < n , m > ~ < a , b > -> Rat a b

num : {n m : Nat} -> Rat n m -> Nat
num (mkrat n _ _) = n

denom : {n m : Nat} -> Rat n m -> Nat
denom (mkrat _ m _) = succ m

rat : {n m : Nat} -> Rat n m -> Nat × Nat
rat (mkrat a b _) = < a , b >

inject : (n : Nat) -> Rat n 0
inject n = mkrat n 0 (rel refl)

rat-equiv : {n m : Nat} -> (p q : Rat n m) -> (rat p) ~ (rat q)
rat-equiv (mkrat a b x) (mkrat c d y) = trans~ x (sym~ y)

injection-proof : {n m : Nat} -> rat (inject n) ~ rat (inject m) -> n ≡ m
injection-proof (rel x) = x

{- Arithmetics of rational numbers -}

_t_ : {a : Nat} -> (b c : Nat) -> Nat
_t_ {a} b c = {!!}

lemma-*-1 : (a b c d : Nat) -> a ≡ b -> c ≡ d -> a * c ≡ b * d
lemma-*-1 a .a c .c refl refl = refl

lemma-*-2-1 : (b c : Nat) -> c * b ≡ b * c
lemma-*-2-1 b c = comm-mult c b

lemma-*-2-2 : (a b c : Nat) -> a * (c * b) ≡ a * ( b * c)
lemma-*-2-2 a b c = cong (λ x -> a * x) (lemma-*-2-1 b c)

lemma-*-2-3 : (a b c : Nat) ->  (a * c) * b ≡ (a * b) * c
lemma-*-2-3 a b c = trans (trans (assoc-mult a c b) (lemma-*-2-2 a b c)) (sym (assoc-mult a b c))

lemma-*-2 : (a b c d : Nat) -> a * b * c * d ≡ a * c * b * d
lemma-*-2 a b c d = cong (λ x -> x * d) (sym (lemma-*-2-3 a b c)) 


_r*_ : {n m k l : Nat} -> (p : Rat n m) -> (q : Rat k l) -> Rat (n * k) (m * l + m + l)
_r*_ {n}{m}{k}{l} (mkrat a b (rel x)) (mkrat c d (rel y)) = mkrat (a * c) (b * d) (rel (trans (trans {!!} {!!}) {!!}))

------------------------------------------

2/2 : Rat 2 1
2/2 = mkrat 2 1 (rel refl)

2/2' : Rat 1 0
2/2' = mkrat 2 1 (rel refl)

1/1 : Rat 1 0
1/1 = mkrat 1 0 (rel refl)

{-
lemma-rat-1 : (n m : Nat) -> n ≡ 0 + 0 * m -> n ≡ 0
lemma-rat-1 .0 zero refl = refl
lemma-rat-1 .(0 + (0 + 0 * m)) (succ m) refl = cong (λ x -> 0 + x) (lemma-rat-1 (0 + 0 * m) m refl)

lemma-trans : {A : Set}{a b c : A} -> a ≡ b -> b ≡ c -> a ≡ c
lemma-trans refl refl = refl

lemma-comm : (n m a : Nat) -> n + m ≡ a -> m + n ≡ a
lemma-comm n m a refl = comm-plus m n

lemma-nat : (n : Nat) -> 0 * n ≡ 0
lemma-nat n = comm-mult 0 n

lemma-nat' : (n : Nat) -> 0 * ( 0 * n ) ≡ 0
lemma-nat' n = lemma-nat (0 * n)

lemma-nat-1 : (n m : Nat) -> 0 * n ≡ 0 * m
lemma-nat-1 zero m = comm-mult m zero
lemma-nat-1 (succ n) m = lemma-comm (zero * n) zero (zero * m) (lemma-nat-1 n m)

lemma-1 : (n m : Nat) -> (0 * m) * n ≡ 0
lemma-1 n m = trans (assoc-mult 0 m n) (trans (comm-mult 0 (m * n)) refl)

lemma' : (n m a c d : Nat) -> c * m ≡ n * d -> a * (c * m) ≡ a * (d * n)
lemma' n m a c d x = cong (λ y -> a * y) (trans x (comm-mult n d))

lemma'' : (n m a c d : Nat) -> a * (c * m) ≡ a * (d * n) -> a * (c * m) ≡ n * (a * d)
lemma'' n m a c d x = trans x (trans (sym (assoc-mult a d n)) (comm-mult (a * d) n))

test : (a b c : Nat) -> a * (b * c) ≡ a * (c * b)
test a b c = cong (λ x -> a * x) (comm-mult b c)

test' : (a b c : Nat) -> a * (b * c) ≡ a * (c * b) -> a * (b * c) ≡ (a * c) * b
test' a b c x = trans x (sym (assoc-mult a c b))

test'' : (a b c : Nat) -> a * (b * c) ≡ a * (c * b) -> a * (b * c) ≡ b * (a * c)
test'' a b c x = {!!}


lemma- : (a b c : Nat) -> a * (b * c) ≡ b * (a * c)
lemma- a b c = {!!}

lemma : (n m a b c d : Nat) -> c * m ≡ n * d -> a * m ≡ n * b -> a * d ≡ c * b
lemma n m a b c d f g = {!!}

--rat-equiv : (n m : Nat) -> (p q : (Rat n m)) -> (rat p) ~ (rat q)
--rat-equiv n m (mkrat n₁ m₁ (rel x)) (mkrat n₂ m₂ (rel y)) = rel {!!}
-}
{-
--rat-equiv zero zero (mkrat .(0 + 0 * m₁) m₁ (rel refl)) (mkrat .(0 + 0 * m₂) m₂ (rel refl)) = rel (trans (assoc-mult (0) (m₁ + 1) (m₂ + 1)) (trans (comm-mult 0 ((m₁ + 1) * (m₂ + 1))) {!!}))
rat-equiv zero zero (mkrat .(0 + 0 * m₁) m₁ (rel refl)) (mkrat .(0 + 0 * m₂) m₂ (rel refl)) = rel (trans (lemma-1 (m₂ + 1) (m₁ + 1)) (trans (lemma-1 (m₁ + {!!}) {!!}) {!!}))
rat-equiv zero (succ m) (mkrat n₁ m₁ x) (mkrat n₂ m₂ x₁) = rel {!!}
rat-equiv (succ n) zero (mkrat n₁ m₁ x) (mkrat n₂ m₂ x₁) = rel {!!}
rat-equiv (succ n) (succ m) (mkrat n₁ m₁ x) (mkrat n₂ m₂ x₁) = rel {!!}
-}
{-
1*1=1*1 : 1 * 1 ≡ 1 * 1
1*1=1*1 = refl

1*2=2*1 : 1 * 2 ≡ 2 * 1
1*2=2*1 = refl

1/1~1/1 : < 1 , 1 > ~ < 1 , 1 >
1/1~1/1 = rel 1 1 1 1 refl

1/1~2/2 : < 1 , 1 > ~ < 2 , 2 >
1/1~2/2 = rel 1 1 2 2 refl

¬1/1~2/1 : < 1 , 1 > ~ < 2 , 1 > -> ⊥
¬1/1~2/1 (rel .1 .1 .2 .1 ())

n+1=1+n : (n : Nat) -> succ n ≡ 1 + n
n+1=1+n zero = refl
n+1=1+n (succ n) = cong succ (n+1=1+n n)

1+n=n+1 : (n : Nat) -> 1 + n ≡ succ n
1+n=n+1 zero = refl
1+n=n+1 (succ n) = cong succ (1+n=n+1 n)

lemma : (n : Nat) -> 1 + 1 * n ≡ (succ (1 * n))
lemma zero = refl
lemma (succ n) = 1+n=n+1 (1 + 1 * n)

lemma' : (n : Nat) -> (succ (1 * n)) ≡ 1 + 1 * n
lemma' zero = refl
lemma' (succ n) = n+1=1+n (1 + 1 * n)

lemma-2 : (n m : Nat) -> n ≡ m -> succ n ≡ 1 + m
lemma-2 zero .0 refl = refl
lemma-2 (succ n) .(succ n) refl = cong succ (lemma-2 n n refl)


n=1*n : (n : Nat) -> n ≡ 1 * n
n=1*n zero = refl
n=1*n (succ n) = lemma-2 n (1 * n) (n=1*n n) 

lemma-3 : (n m : Nat) -> n ≡ m -> n ≡ 1 * m
lemma-3 n .n refl = n=1*n n

n/1~m/1 : {n m : Nat} -> n ≡ m -> < n , 1 > ~ < m , 1 >
n/1~m/1 {n}{m} x = rel n 1 m 1 (lemma-3 n m x)
-}





