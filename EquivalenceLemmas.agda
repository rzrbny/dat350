module EquivalenceLemmas where

open import Bool
open import Nat
open import Identity
open import PropositionalLogic
open import Product

postulate comm-plus : (n m : Nat) -> n + m ≡ m + n
postulate comm-mult : (n m : Nat) -> n * m ≡ m * n
postulate assoc-plus : (n m l : Nat) -> (n + m) + l ≡ n + (m + l)
postulate assoc-mult : (n m l : Nat) -> (n * m) * l ≡ n * (m * l)


{- lemmas for proof of transitivity of _~_ -}

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

{- lemmas for proof of r* -}

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

