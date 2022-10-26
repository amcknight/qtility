open import Data.Rational

module utility {e : Set} (utility : e -> ℚ) where

open import uniform
open import Data.Integer using (+_; -[1+_]; ℤ; 0ℤ)
open import Data.List
open import Data.Product
open import Data.Nat using (suc; s≤s; z≤n; ℕ)
open import Data.Rational.Properties
open import Relation.Binary.PropositionalEquality

odds→rat : Odds -> ℚ
odds→rat (odds numer (suc denom) denom≠0 numer≤denom) = (+ numer) / (suc denom)

score : Dist e -> ℚ
score x = foldr (λ {(e , o) s → s + odds→rat o * utility e}) 0ℚ (probs x)

data _⊑_ : Dist e -> Dist e -> Set where
  prefers : (d1 : Dist e) -> (d2 : Dist e) -> score d1 ≤ score d2 -> d1 ⊑ d2

open import pref _⊑_
open import Relation.Nullary
open import Data.Sum

postulate
  bias≤ : (d1 d2 d3 : Dist e) -> (o : Odds) -> score d1 ≤ score d2 -> score (bias o d1 d3) ≤ score (bias o d2 d3)
  ⋆-pres-+ : {q r : ℚ} -> (NonNegative q) -> (NonNegative r) -> NonNegative (q * r)
  /-pres-+ : {q : ℚ} -> (NonNegative q) -> NonNegative (1/ q)
  +ℤℕ : {i : ℤ} -> (i Data.Integer.≥ 0ℤ) -> ℕ

≤→nonneg : {b c : ℚ} -> (b ≤ c) -> (0ℚ ≤ c - b)
≤→nonneg {b} {c} b≤c =
  begin
    0ℚ       ≡⟨ sym (+-inverseʳ c) ⟩
    c + - c  ≡⟨⟩
    c - c    ≤⟨ +-monoʳ-≤ c (neg-antimono-≤ b≤c) ⟩
    c + - b  ≡⟨⟩
    c - b    ∎
  where open ≤-Reasoning

cont-score : (a b c : Dist e) -> (score a ≤ score b) -> (score b ≤ score c) -> (¬ (score a ≡ score c)) -> Odds
cont-score a b c sab sbc sa≠sc = let
    u = ((score c - score b) * 1/ (score c - score a))
    x = ≤→nonneg sab
    y = ≤→nonneg sbc

  in odds {!   !} {!   !} {!   !} {!   !}

cont-score-+ : (q r s : ℚ) -> q ≤ r -> r ≤ s -> ℚ.numerator ((s - r) * 1/ (s - q)) Data.Integer.≥ 0ℤ
cont-score-+ = {!   !}

-- ↥

eq→less : (q r : ℚ) -> q ≡ r -> q ≤ r × r ≤ q
eq→less q .q refl = ≤-refl , ≤-refl

vnm : VNM
VNM.refl vnm a = prefers a a ≤-refl
VNM.comp vnm a b with ≤-total (score a) (score b)
... | inj₁ x = inj₁ (prefers a b x)
... | inj₂ y = inj₂ (prefers b a y)
VNM.trans vnm a b c (prefers .a .b ab) (prefers .b .c bc) = prefers a c (≤-trans ab bc)
VNM.cont vnm a b c (prefers .a .b sab) (prefers .b .c sbc) = (cont-score a b c sab sbc {!   !}) , prefers _ _ (≤-reflexive {!   !}) , prefers _ _ (≤-reflexive {!   !})
VNM.indep vnm a b c (prefers .a .b ab) o = prefers (bias o a c) (bias o b c) (bias≤ a b c o ab)

_ : ((+ 3 / 10) - (+ 6 / 10)) * 1/ ((+ 2 / 10) - (+ 6 / 10)) ≡  ((+ 6 / 10) - (+ 3 / 10)) * 1/ ((+ 6 / 10) - (+ 2 / 10))
_ = refl
