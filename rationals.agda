{-# OPTIONS --rewriting --prop #-}

open import setoid_rr
open import Agda.Builtin.Nat

ℚ-carrier : Set
ℚ-carrier = prod Nat Nat

ℚ-rel : ℚ-carrier → ℚ-carrier → Prop
ℚ-rel (a , b) (c , d) = Id Nat (a * (suc d)) (c * (suc b))

ℚ-rel-refl : (x : ℚ-carrier) → ℚ-rel x x
ℚ-rel-refl (a , b) = Id-refl (a * (suc b))

postulate ℚ-rel-sym : (x y : ℚ-carrier) → ℚ-rel x y → ℚ-rel y x
postulate ℚ-rel-trans : (x y z : ℚ-carrier) → ℚ-rel x y → ℚ-rel y z → ℚ-rel x z

postulate lia : (n m : Nat) → Id Nat n m

ℚ-quotient : quotient-data _
ℚ-quotient = q-data ℚ-carrier ℚ-rel ℚ-rel-refl ℚ-rel-sym ℚ-rel-trans

ℚ : Set
ℚ = Quotient ℚ-quotient

+ℚ-carrier : ℚ-carrier → ℚ-carrier → ℚ-carrier
+ℚ-carrier (a , b) (c , d) = (a * (suc d) + c * (suc b) , b * d + b + d)

+ℚ-carrier-compat : (x x' y y' : ℚ-carrier) → ℚ-rel x x' → ℚ-rel y y' → ℚ-rel (+ℚ-carrier x y) (+ℚ-carrier x' y')
+ℚ-carrier-compat (a , b) (a' , b') (c , d) (c' , d') e e' =
  lia (((a * (suc d) + c * (suc b)) * suc (b' * d' + b' + d')))
    (((a' * (suc d') + c' * (suc b')) * suc (b * d + b + d)))


_+ℚ_ : ℚ → ℚ → ℚ
_+ℚ_ = Quotient-elim2 ℚ-quotient (λ _ _ → ℚ) (λ x y → pi (+ℚ-carrier x y)) +ℚ-carrier-compat
