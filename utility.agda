open import Data.Rational

module utility {e : Set} (utility : e -> ℚ) where

open import uniform
open import Data.Integer using (+_)
open import Data.List
open import Data.Product
open import Data.Nat using (suc)
open import Data.Rational.Properties

odds→rat : Odds -> ℚ
odds→rat (odds numer (suc denom) denom≠0 numer≤denom) = (+ numer) / (suc denom)

score : Dist e -> ℚ
score x = foldr (λ {(e , o) s → s + odds→rat o * utility e}) 0ℚ (probs x)

data _⊑_ : Dist e -> Dist e -> Set where
  prefers : (d1 : Dist e) -> (d2 : Dist e) -> score d1 ≤ score d2 -> d1 ⊑ d2

open import pref _⊑_
open import Relation.Nullary
open import Data.Bool hiding (_≤?_)
open import Data.Sum

vnm : VNM
VNM.refl vnm a = prefers a a ≤-refl
VNM.comp vnm a b with ≤-total (score a) (score b)
... | inj₁ x = inj₁ (prefers a b x)
... | inj₂ y = inj₂ (prefers b a y)
VNM.trans vnm a b c (prefers .a .b ab) (prefers .b .c bc) = prefers a c (≤-trans ab bc)
VNM.cont vnm = {!   !}
VNM.indep vnm = {!   !}