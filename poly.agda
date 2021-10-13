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

    +0R : (r : R) → r + 0R ≡ r
    0R+ : (r : R) → 0R + r ≡ r

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


  _+prepoly_ : prepoly → prepoly → prepoly
  [] +prepoly q = q
  p@(_ ∷ _) +prepoly [] = p
  (r ∷ p) +prepoly (r′ ∷ q) = r + r′ ∷ p +prepoly q

  +prepoly-is-nullˡ : (p q : prepoly) → is-null q → up-to-trailing-0 (p +prepoly q) p
  +prepoly-is-nullˡ [] q nq = up-to-null nq nil-is-null
  +prepoly-is-nullˡ p@(_ ∷ _) .[] nil-is-null = up-to-trailing-0-refl p
  +prepoly-is-nullˡ (x ∷ p) .(0R ∷ _) (0::-is-null nq) rewrite +0R x = up-to-cons x (+prepoly-is-nullˡ p _ nq)

  +prepoly-is-nullʳ : (p q : prepoly) → is-null p → up-to-trailing-0 (p +prepoly q) q
  +prepoly-is-nullʳ [] q np = up-to-trailing-0-refl q
  +prepoly-is-nullʳ p@(_ ∷ _) [] np = up-to-null np nil-is-null
  +prepoly-is-nullʳ .(0R ∷ _) (x ∷ q) (0::-is-null np) rewrite 0R+ x = up-to-cons x (+prepoly-is-nullʳ _ q np)


  +prepoly-compat : (p p′ q q′ : prepoly) → up-to-trailing-0 p p′ → up-to-trailing-0 q q′ → up-to-trailing-0 (p +prepoly q) (p′ +prepoly q′)
  +prepoly-compat p p′ q q′ (up-to-null np np′) hq =
    up-to-trailing-0-trans _ _ _ (+prepoly-is-nullʳ p q np) (up-to-trailing-0-trans _ _ _ hq (up-to-trailing-0-sym _ _ (+prepoly-is-nullʳ p′ q′ np′)))
  +prepoly-compat .(_ ∷ _) .(_ ∷ _) q q′ hp@(up-to-cons _ _) (up-to-null nq nq′) =
    up-to-trailing-0-trans _ _ _ (+prepoly-is-nullˡ _ q nq) (up-to-trailing-0-trans _ _ _ hp (up-to-trailing-0-sym _ _ (+prepoly-is-nullˡ _ q′ nq′)))
  +prepoly-compat .(r ∷ _) .(r ∷ _) .(r′ ∷ _) .(r′ ∷ _) (up-to-cons r hp) (up-to-cons r′ hq) =
    up-to-cons (r + r′) (+prepoly-compat _ _ _ _ hp hq)

  _+P_ : poly → poly → poly
  _+P_ = Quotient-rec2 poly-quotient poly (λ x y → pi (x +prepoly y)) +prepoly-compat

