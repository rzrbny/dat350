module EquivalenceRelation where

open import Bool
open import Nat
open import Identity
open import PropositionalLogic
open import Product

open import EquivalenceLemmas

{- poustulated relations of multiplication and addition on natural numbers
postulate comm-plus : (n m : Nat) -> n + m ≡ m + n
postulate comm-mult : (n m : Nat) -> n * m ≡ m * n
postulate assoc-plus : (n m l : Nat) -> (n + m) + l ≡ n + (m + l)
postulate assoc-mult : (n m l : Nat) -> (n * m) * l ≡ n * (m * l)
-}

{- equivalence relation for pairs of natural numbers -}

data _~_ : Nat × Nat -> Nat × Nat -> Set where
  rel : {a b c d : Nat} -> a * (d + 1) ≡ c * (b + 1) -> < a , b > ~ < c , d >

refl~ : {p : Nat × Nat} -> p ~ p
refl~ {< _ , _ >} = rel refl

sym~ : {p q : Nat × Nat} -> p ~ q -> q ~ p
sym~ (rel x) = rel (sym x)

lemma-trans :  (a b c d e f : Nat) -> a * succ d ≡ c * b -> c * f ≡ e * succ d -> a * f ≡ e * b
lemma-trans a b c d e f x y = lemma-3 a b c d e f x y

trans~ : {p q r : Nat × Nat} -> p ~ q -> q ~ r -> p ~ r
trans~ {< a , b >} {< c , d >} {< e , f >} (rel x) (rel y) = rel (lemma-trans a (succ b) c d e (succ f) x y)

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

------------------------------

2/2 : Rat 2 1
2/2 = mkrat 2 1 (rel refl)

2/2' : Rat 1 0
2/2' = mkrat 2 1 (rel refl)

1/1 : Rat 1 0
1/1 = mkrat 1 0 (rel refl)

3/1 = inject 3

{- some simple proofs -}

rat-equiv : {n m : Nat} -> (p q : Rat n m) -> (rat p) ~ (rat q)
rat-equiv (mkrat a b x) (mkrat c d y) = trans~ x (sym~ y)

rat-equiv-class : {n m k l : Nat} -> (p : Rat n m) -> (q : Rat k l) -> (rat p) ~ (rat q) -> (eqc p) ~ (eqc q) --< n , m > ~ < k , l >
rat-equiv-class (mkrat _ _ x) (mkrat _ _ y) z = trans~ (trans~ (sym~ x) z) y

injection-proof : {n m : Nat} -> rat (inject n) ~ rat (inject m) -> n ≡ m
injection-proof (rel x) = x

injection-proof' : {n m : Nat} -> eqc (inject n) ~ eqc (inject m) -> n ≡ m
injection-proof' (rel x) = x

{- arithmetics (multiplication) of rational numbers -}

_r*_ : {n m k l : Nat} -> (p : Rat n m) -> (q : Rat k l) -> Rat (n * k) (m * l + m + l)
_r*_ {n}{m}{k}{l} (mkrat a b (rel x)) (mkrat c d (rel y)) = mkrat (a * c) (b * d + b + d)
     (rel (trans (trans
       (sym
       (trans (trans (sym (assoc-mult (a * succ m) c (succ l))) (lemma-*-2 a (succ m) c (succ l)))
         (trans (assoc-mult (a * c) (succ m) (succ l)) (cong (λ x -> (a * c) * x) (lemma-*-3 m l))))) (
       lemma-*-1 x y))
       (trans (trans (sym (assoc-mult (n * succ b) k (succ d))) (lemma-*-2 n (succ b) k (succ d)))
         (trans (assoc-mult (n * k) (succ b) (succ d)) (cong (λ x -> (n * k) * x) (lemma-*-3 b d))))))

comm-rmult : {n m k l : Nat}(p : Rat n m )(q : Rat k l) -> eqc (p r* q) ~ eqc (q r* p)
comm-rmult {n}{m}{k}{l} p q = rel (trans (trans
  (trans (sym (cong (λ x -> (n * k) * x) (lemma-*-3 l m))) (sym (assoc-mult (n * k) (succ l) (succ m))))
  (trans (trans (assoc-mult (n * k) (succ l) (succ m)) (cong (λ x -> x * (succ l * succ m))
    (comm-mult n k))) (cong (λ x -> k * n * x) (lemma-*-3 l m))))
  (cong (λ x -> (k * n) * x) (trans (sym (lemma-*-3 l m)) (trans (comm-mult (succ l) (succ m)) (lemma-*-3 m l)))))

{- some properties of our rational numbers -}

mult-identity : Nat -> Set
mult-identity m = Rat (succ m) m

mult-inverse : {n m : Nat} -> (p : Rat (succ n) m) -> Set
mult-inverse {n} {m} p = Rat (succ m) n

identity-proof : {n k l : Nat} -> (p : mult-identity n) -> (q : Rat k l) -> eqc q ~ eqc (p r* q)
identity-proof {n}{k}{l} (mkrat _ _ _) (mkrat _ _ _) = rel
  (trans (cong (λ x -> k * x) (sym (lemma-*-3 n l)))
         (trans (sym (assoc-mult k (succ n) (succ l)))
                (cong (λ x -> x * succ l) (comm-mult k (succ n)))))

inverse-proof : {n m k : Nat} -> {id : mult-identity k} -> (p : Rat (succ n) m) -> (q : mult-inverse p) ->  eqc (p r* q) ~ eqc id
inverse-proof {n} {m} {k} {id} p q = rel
  (trans
    (cong (λ x -> x * succ k) (comm-mult (succ n) (succ m)))
    (trans
      (comm-mult (succ m * succ n) (succ k))
      (cong (λ x -> succ k * x) (lemma-*-3 m n))))

mult-extension : (n m : Nat) -> eqc (inject (n * m)) ~ eqc ((inject n) r* (inject m))
mult-extension n m = rel refl

---------------------------------------------------



