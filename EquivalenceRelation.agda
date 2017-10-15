module EquivalenceRelation where

open import Bool
open import Nat
open import Identity
open import PropositionalLogic

postulate comm-plus : (n m : Nat) -> n + m ≡ m + n
postulate comm-mult : (n m : Nat) -> n * m ≡ m * n
postulate assoc-plus : (n m l : Nat) -> (n + m) + l ≡ n + (m + l)
postulate assoc-mult : (n m l : Nat) -> (n * m) * l ≡ n * (m * l)

{- equivalence relation for pairs of natural numbers -}

data _~_ : Nat × Nat -> Nat × Nat -> Set where
  rel : {a b c d : Nat} -> a * (d + 1) ≡ c * (b + 1) -> < a , b > ~ < c , d >

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
num (mkrat a _ _) = a

denom : {n m : Nat} -> Rat n m -> Nat
denom (mkrat _ b _) = succ b

rat : {n m : Nat} -> Rat n m -> Nat × Nat
rat (mkrat a b _) = < a , b >

eqc : {n m : Nat} -> Rat n m -> Nat × Nat
eqc {n}{m} _ = < n , m >

inject : (n : Nat) -> Rat n 0
inject n = mkrat n 0 (rel refl)


{- Some simple proofs -}

rat-equiv : {n m : Nat} -> (p q : Rat n m) -> (rat p) ~ (rat q)
rat-equiv (mkrat a b x) (mkrat c d y) = trans~ x (sym~ y)

rat-equiv-class : {n m k l : Nat} -> (p : Rat n m) -> (q : Rat k l) -> (rat p) ~ (rat q) -> (eqc p) ~ (eqc q)
rat-equiv-class {n}{m}{k}{l} (mkrat a b x) (mkrat c d y) z = trans~ (trans~ (sym~ x) z) y

rat-equiv' : {n m : Nat} -> (p q : Rat n m) -> (eqc p) ~ (eqc q)
rat-equiv' (mkrat a b x) (mkrat c d y) = rel refl


injection-proof : {n m : Nat} -> rat (inject n) ~ rat (inject m) -> n ≡ m
injection-proof (rel x) = x

injection-proof' : {n m : Nat} -> eqc (inject n) ~ eqc (inject m) -> n ≡ m
injection-proof' (rel x) = x


{- Arithmetics of rational numbers -}

lemma-*-1 : {a b c d : Nat} -> a ≡ b -> c ≡ d -> a * c ≡ b * d
lemma-*-1 {a} {.a} {c} {.c} refl refl = refl

lemma-*-2-1 : (b c : Nat) -> c * b ≡ b * c
lemma-*-2-1 b c = comm-mult c b

lemma-*-2-2 : (a b c : Nat) -> a * (c * b) ≡ a * ( b * c)
lemma-*-2-2 a b c = cong (λ x -> a * x) (lemma-*-2-1 b c)

lemma-*-2-3 : (a b c : Nat) ->  (a * c) * b ≡ (a * b) * c
lemma-*-2-3 a b c = trans (trans (assoc-mult a c b) (lemma-*-2-2 a b c)) (sym (assoc-mult a b c))

lemma-*-2 : (a b c d : Nat) -> a * b * c * d ≡ a * c * b * d
lemma-*-2 a b c d = cong (λ x -> x * d) (sym (lemma-*-2-3 a b c))

lemma-*-3 : (b c : Nat) -> succ b * succ c ≡ (b * c + b + c + 1)
lemma-*-3 b c = trans (comm-plus (succ b) (succ b * c))
                      (cong succ (trans (cong (λ x -> x + b)
                                        (comm-mult (succ b) c))
                                        (trans (trans (assoc-plus c (c * b) b)
                                        (comm-plus c (c * b + b))) (cong (λ x -> x + b + c) (comm-mult c b)))))

_r*_ : {n m k l : Nat} -> (p : Rat n m) -> (q : Rat k l) -> Rat (n * k) (m * l + m + l)
_r*_ {n}{m}{k}{l} (mkrat a b (rel x)) (mkrat c d (rel y)) = mkrat (a * c) (b * d + b + d)
     (rel (trans (trans
       (sym
       (trans (trans (sym (assoc-mult (a * succ m) c (succ l))) (lemma-*-2 a (succ m) c (succ l)))
         (trans (assoc-mult (a * c) (succ m) (succ l)) (cong (λ x -> (a * c) * x) (lemma-*-3 m l))))) (
       lemma-*-1 x y))
       (trans (trans (sym (assoc-mult (n * succ b) k (succ d))) (lemma-*-2 n (succ b) k (succ d)))
         (trans (assoc-mult (n * k) (succ b) (succ d)) (cong (λ x -> (n * k) * x) (lemma-*-3 b d))))))

_r*'_ : {n m k l : Nat} -> (p : Rat n m) -> (q : Rat k l) -> Rat (n * k) (m * l + m + l)
_r*'_ {n} {m} {k} {l} (mkrat a b x) (mkrat c d y) = mkrat (a * c) (b * d + b + d) {!!}

{-
3/7 * 11/2 = 33/14
Rat 3 6 * Rat 11 1 = Rat 33 13
-}

comm-rmult : {n m k l : Nat}(p : Rat n m )(q : Rat k l) -> eqc (p r* q) ~ eqc (q r* p)
comm-rmult {n}{m}{k}{l} p q = rel (trans (trans
  (trans (sym (cong (λ x -> (n * k) * x) (lemma-*-3 l m))) (sym (assoc-mult (n * k) (succ l) (succ m))))
  (trans (trans (assoc-mult (n * k) (succ l) (succ m)) (cong (λ x -> x * (succ l * succ m))
    (comm-mult n k))) (cong (λ x -> k * n * x) (lemma-*-3 l m))))
  (cong (λ x -> (k * n) * x) (trans (sym (lemma-*-3 l m)) (trans (comm-mult (succ l) (succ m)) (lemma-*-3 m l)))))

{- Some properties of our rational numbers -}

identity : Nat -> Set
identity m = Rat (succ m) m

identity-proof : {n k l : Nat} -> (p : identity n) -> (q : Rat k l) -> eqc q ~ eqc (p r* q)
identity-proof {n}{k}{l} (mkrat _ _ _) (mkrat _ _ _) = rel
  (trans (cong (λ x -> k * x) (sym (lemma-*-3 n l)))
         (trans (sym (assoc-mult k (succ n) (succ l)))
                (cong (λ x -> x * succ l) (comm-mult k (succ n)))))

inverse : {n m : Nat} -> (p : Rat (succ n) m) -> Set
inverse {n} {m} p = Rat (succ m) n

inverse-proof : {n m k : Nat} -> {id : identity k} -> (p : Rat (succ n) m) -> (q : inverse p) ->  eqc (p r* q) ~ eqc id
inverse-proof {n} {m} {k} {id} p q = rel
  (trans
    (cong (λ x -> x * succ k) (comm-mult (succ n) (succ m)))
    (trans
      (comm-mult (succ m * succ n) (succ k))
      (cong (λ x -> succ k * x) (lemma-*-3 m n))))

mult-extension : (n m : Nat) -> eqc (inject (n * m)) ~ eqc ((inject n) r* (inject m))
mult-extension n m = rel refl

---------------------------------------------------

2/2 : Rat 2 1
2/2 = mkrat 2 1 (rel refl)

2/2' : Rat 1 0
2/2' = mkrat 2 1 (rel refl)

1/1 : Rat 1 0
1/1 = mkrat 1 0 (rel refl)




