{-# OPTIONS --rewriting --prop #-}

open import setoid_rr
open import Agda.Builtin.Nat

carrier : Set
carrier = prod Nat Nat

rel : carrier → carrier → Prop
rel (a , b) (c , d) = Id Nat (a * (suc d)) (c * (suc b))

rel-refl : (x : carrier) → rel x x
rel-refl (a , b) = Id-refl (a * (suc b))

postulate rel-sym : (x y : carrier) → rel x y → rel y x
postulate rel-trans : (x y z : carrier) → rel x y → rel y z → rel x z

postulate lia : (n m : Nat) → Id Nat n m

ℚ : Set
ℚ = Quotient carrier rel rel-refl rel-sym rel-trans

+carrier : carrier → carrier → carrier
+carrier (a , b) (c , d) = (a * (suc d) + c * (suc b) , b * d + b + d)

+carrier-compat : (x x' y y' : carrier) → rel x x' → rel y y' → rel (+carrier x y) (+carrier x' y')
+carrier-compat (a , b) (a' , b') (c , d) (c' , d') e e' =
  lia (((a * (suc d) + c * (suc b)) * suc (b' * d' + b' + d')))
    (((a' * (suc d') + c' * (suc b')) * suc (b * d + b + d)))

Quotient-elim2 : (A : Set ℓ)
                 (R : A → A → Prop ℓ)
                 (r : (x : A) → R x x)
                 (s : (x y : A) → R x y → R y x)
                 (t : (x y z : A) → R x y → R y z → R x z)
                 (P : Quotient A R r s t → Quotient A R r s t → Set ℓ₁)
                 (p : (x y : A) → P (pi A R r s t x) (pi A R r s t y))
                 (e : (x x' y y' : A) → (rel1 : R x x') → (rel2 : R y y') →
                         Id _ (transport-Id (P (pi A R r s t x')) (pi A R r s t y) (transport-Id (λ x → P x (pi A R r s t y)) (pi A R r s t x) (p x y) (pi A R r s t x') rel1) (pi A R r s t y') rel2) (p x' y'))
                 (w w' : Quotient A R r s t) → P w w'
Quotient-elim2 A R r s t P p e w w' = {!!}

_+ℚ_ : ℚ → ℚ → ℚ
_+ℚ_ = Quotient-elim2 carrier rel rel-refl rel-sym rel-trans (λ x y → ℚ) (λ x y → pi carrier rel rel-refl rel-sym rel-trans (+carrier x y)) {!!} --+carrier-compat
