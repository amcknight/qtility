open import Data.Rational

module utility {e : Set} (utility : e -> ℚ) where

open import uniform
open import Data.Integer using (+_; -[1+_]; ℤ; 0ℤ)
open import Data.List
open import Data.Product hiding (map)
open import Data.Nat using (suc; s≤s; z≤n; ℕ)
open import Data.Rational.Properties
open import Relation.Binary.PropositionalEquality

odds→rat : Odds -> ℚ
odds→rat (odds numer (suc denom) denom≠0 numer≤denom) = (+ numer) / (suc denom)

sumℚ : List ℚ → ℚ
sumℚ = foldr _+_ 0ℚ

expected : e × Odds → ℚ
expected (e , o) = odds→rat o * utility e

score : Dist e -> ℚ
score x = sumℚ (map expected (probs x))

score-always : (ev : e) → score (always ev) ≡ utility ev
score-always ev =
  begin
    score (always ev)                                 ≡⟨⟩
    sumℚ (map expected (probs (always ev)))           ≡⟨⟩
    sumℚ (map expected (probs' maxOdds (always ev)))  ≡⟨⟩
    sumℚ (map expected ((ev , maxOdds) ∷ []))         ≡⟨⟩
    sumℚ (expected (ev , maxOdds) ∷ [])               ≡⟨⟩
    sumℚ ((odds→rat maxOdds * utility ev) ∷ [])       ≡⟨⟩
    (odds→rat maxOdds * utility ev) + 0ℚ              ≡⟨ +-identityʳ (odds→rat maxOdds * utility ev) ⟩
    (odds→rat maxOdds * utility ev)                   ≡⟨⟩
    1ℚ * utility ev                                   ≡⟨ *-identityˡ (utility ev) ⟩
    utility ev                                        ∎
  where open ≡-Reasoning

record _⊑_ (d1 d2 : Dist e) : Set where
  constructor prefers
  field
    better-score : score d1 ≤ score d2

open import pref _⊑_
open import Relation.Nullary
open import Data.Sum

postulate
  bias≤ : (d1 d2 d3 : Dist e)  → (o : Odds) → score d1 ≤ score d2 → score (bias o d1 d3) ≤ score (bias o d2 d3)

⋆-pres-+ : {q r : ℚ} → 0ℚ ≤ q → 0ℚ ≤ r → 0ℚ ≤ (q * r)
⋆-pres-+ {q} {r} q≥0 r≥0 =
  begin
    0ℚ       ≡⟨⟩
    0ℚ * 0ℚ  ≤⟨ *-monoʳ-≤-nonNeg 0ℚ _ q≥0 ⟩
    q * 0ℚ   ≤⟨ *-monoˡ-≤-nonNeg q (nonNegative q≥0) r≥0 ⟩
    q * r    ∎
  where open ≤-Reasoning

/-pres-+ : (q : ℚ) -> ∀ {n≠0} → Positive q → Positive (1/_ q {n≠0})
/-pres-+ q = pos⇒1/pos q

≤→nonneg : {b c : ℚ} → (b ≤ c) → (0ℚ ≤ c - b)
≤→nonneg {b} {c} b≤c =
  begin
    0ℚ       ≡⟨ sym (+-inverseʳ c) ⟩
    c + - c  ≤⟨ +-monoʳ-≤ c (neg-antimono-≤ b≤c) ⟩
    c + - b  ≡⟨⟩
    c - b    ∎
  where open ≤-Reasoning

+ℤℕ : (i : ℤ) -> (i Data.Integer.≥ 0ℤ) -> ℕ
+ℤℕ (+_ n) x = n

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
VNM.refl vnm a = prefers ≤-refl
VNM.comp vnm a b with ≤-total (score a) (score b)
... | inj₁ x = inj₁ (prefers x)
... | inj₂ y = inj₂ (prefers y)
VNM.trans vnm a b c (prefers ab) (prefers bc) = prefers (≤-trans ab bc)
VNM.cont vnm a b c (prefers sab) (prefers sbc) = (cont-score a b c sab sbc {!   !}) , prefers (≤-reflexive {!   !}) , prefers (≤-reflexive {!   !})
VNM.indep vnm a b c (prefers ab) o = prefers (bias≤ a b c o ab)

_ : ((+ 3 / 10) - (+ 6 / 10)) * 1/ ((+ 2 / 10) - (+ 6 / 10)) ≡  ((+ 6 / 10) - (+ 3 / 10)) * 1/ ((+ 6 / 10) - (+ 2 / 10))
_ = refl
