{-# OPTIONS --rewriting --prop #-}

open import setoid_rr
open import Agda.Builtin.Equality
open import Agda.Builtin.List

{- inspired by the polynomial example in cubical agda from https://www.youtube.com/watch?v=p9ANNglWMvc -}


record cring : Set₁ where
  field
    R : Set
    _+_ : R → R → R
    _*_ : R → R → R
    0R : R
    1R : R

    -- missing laws


module _ (cR : cring) where
  open cring cR public

  prepoly : Set
  prepoly = List R


  data is-null : prepoly → Prop where
    nil-is-null : is-null []
    0::-is-null : {l : prepoly} → is-null l → is-null (0R ∷ l)

  data up-to-trailing-0 : prepoly → prepoly → Prop where
    up-to-null : {l l' : prepoly} → is-null l → is-null l' → up-to-trailing-0 l l'
    up-to-cons : {l l' : prepoly}(r : R) → up-to-trailing-0 l l' → up-to-trailing-0 (r ∷ l) (r ∷ l')


  up-to-trailing-0-refl : (x : prepoly) → up-to-trailing-0 x x
  up-to-trailing-0-refl [] = up-to-null nil-is-null nil-is-null
  up-to-trailing-0-refl (r ∷ x) = up-to-cons r (up-to-trailing-0-refl x)

  up-to-trailing-0-sym : (x y : prepoly) → up-to-trailing-0 x y → up-to-trailing-0 y x
  up-to-trailing-0-sym x y (up-to-null nx ny) = up-to-null ny nx
  up-to-trailing-0-sym .(r ∷ _) .(r ∷ _) (up-to-cons r hxy) = up-to-cons r (up-to-trailing-0-sym _ _ hxy)


  up-to-trailing-0-null-is-null : {l l' : prepoly} → up-to-trailing-0 l l' → is-null l → is-null l'
  up-to-trailing-0-null-is-null (up-to-null _ n) _ = n
  up-to-trailing-0-null-is-null (up-to-cons .(0R) hxy) (0::-is-null n) = 0::-is-null (up-to-trailing-0-null-is-null hxy n)

  up-to-trailing-0-trans : (x y z : prepoly) → up-to-trailing-0 x y → up-to-trailing-0 y z → up-to-trailing-0 x z
  up-to-trailing-0-trans x y z (up-to-null nx ny) hyz = up-to-null nx (up-to-trailing-0-null-is-null hyz ny)
  up-to-trailing-0-trans .(r ∷ _) .(r ∷ _) z hxy@(up-to-cons r _) (up-to-null ny nz) =
    up-to-null (up-to-trailing-0-null-is-null (up-to-trailing-0-sym _ _ hxy) ny) nz
  up-to-trailing-0-trans .(r ∷ _) .(r ∷ _) .(r ∷ _) (up-to-cons r hxy) (up-to-cons .r hyz) =
    up-to-cons r (up-to-trailing-0-trans _ _ _ hxy hyz)

  poly-quotient : quotient-data _
  carrier poly-quotient = prepoly
  rel poly-quotient = up-to-trailing-0
  rel-refl poly-quotient = up-to-trailing-0-refl
  rel-sym poly-quotient = up-to-trailing-0-sym
  rel-trans poly-quotient = up-to-trailing-0-trans

  poly : Set
  poly = Quotient poly-quotient
