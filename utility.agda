open import Data.Rational

module utility {e : Set} (utility : e -> ℚ) where

open import Function using (_∘_)
open import uniform
open import Data.Integer using (+_; -[1+_]; ℤ; 0ℤ)
open import Data.List
open import Data.List.Properties
open import Data.Product hiding (map)
import Data.Nat.Properties
open import Data.Nat using (suc; s≤s; z≤n; ℕ)
open import Data.Rational.Properties
open import Relation.Binary.PropositionalEquality
open import Data.Rational.Unnormalised.Base using (_≢0)

postulate
  todo : {A : Set} → A

open import Data.Unit using (tt)

build-≢0 : (n : ℕ) → (0 Data.Nat.< n) → n ≢0
build-≢0 .(suc _) (s≤s x) = tt

odds→rat : Odds -> ℚ
odds→rat (odds numer denom denom≠0 numer≤denom) = _/_ (+ numer) denom { build-≢0 denom denom≠0 }

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

sumℚ-homo : (a b : List ℚ) → sumℚ (a ++ b) ≡ sumℚ a + sumℚ b
sumℚ-homo [] b = sym (+-identityˡ (sumℚ b))
sumℚ-homo (x ∷ a) b =
  begin
    sumℚ (x ∷ a ++ b)      ≡⟨⟩
    x + sumℚ (a ++ b)      ≡⟨ cong (_+_ x) (sumℚ-homo a b) ⟩
    x + (sumℚ a + sumℚ b)  ≡⟨ sym (+-assoc x (sumℚ a) (sumℚ b)) ⟩
    (x + sumℚ a) + sumℚ b  ≡⟨⟩
    sumℚ (x ∷ a) + sumℚ b  ∎
  where open ≡-Reasoning

*-/-distrib
  : ∀ n1 n2 d1 d2
  → (d1ne : d1 Data.Nat.> 0) (d2ne : d2 Data.Nat.> 0)
  → (_/_ (+ (n1 Data.Nat.* n2)) (d1 Data.Nat.* d2) {build-≢0 (d1 Data.Nat.* d2) ( Data.Nat.Properties.*-mono-≤ d1ne d2ne )})
  ≡ (_/_ (+ n1) d1 {build-≢0 d1 d1ne}) * (_/_ (+ n2) d2 {build-≢0 d2 d2ne})
*-/-distrib n1 n2 d1 d2 d1ne d2ne =
  begin
    normalize (n1 Data.Nat.* n2) (d1 Data.Nat.* d2)
  ≡⟨ todo ⟩
    normalize n1 d1 * normalize n2 d2
  ∎
  where open ≡-Reasoning

⊗-homo : ∀ a b → odds→rat (a ⊗ b) ≡ odds→rat a * odds→rat b
⊗-homo a@(odds an ad (s≤s ax) ay) b@(odds bn bd (s≤s bx) by) =
  begin
    odds→rat (a ⊗ b)                             ≡⟨⟩
    (+ (an Data.Nat.* bn)) / (ad Data.Nat.* bd)  ≡⟨ *-/-distrib an bn ad bd (s≤s z≤n) (s≤s z≤n) ⟩
    (+ an / ad) * (+ bn / bd)                    ≡⟨⟩
    odds→rat a * odds→rat b                      ∎
  where open ≡-Reasoning

sumℚ-factor : {A : Set} (k : ℚ) (x : List ℚ) → sumℚ (map (k *_) x) ≡ k * sumℚ x
sumℚ-factor k [] = sym (*-zeroʳ k)
sumℚ-factor {A} k (x ∷ xs) =
  begin
    sumℚ (map (k *_) (x ∷ xs))    ≡⟨⟩
    k * x + sumℚ (map (k *_) xs)  ≡⟨ cong (\ φ → k * x + φ) (sumℚ-factor {A} k xs) ⟩
    k * x + (k * sumℚ xs)         ≡⟨ sym (*-distribˡ-+ k x (sumℚ xs)) ⟩
    k * (x + sumℚ xs)             ≡⟨⟩
    k * sumℚ (x ∷ xs)
  ∎
  where open ≡-Reasoning

score-bias : (d1 d2 : Dist e) → (o : Odds) → score (bias o d1 d2) ≡ odds→rat o * score d1 + (1ℚ - odds→rat o) * score d2
score-bias d1 d2 o =
  begin
    score (bias o d1 d2)
  ≡⟨⟩
    sumℚ (map expected (probs (bias o d1 d2)))
  ≡⟨⟩
    sumℚ (map expected (probs' maxOdds (bias o d1 d2)))
  ≡⟨⟩
    let lhsp = probs' maxOdds d1
        lhs = Data.List.map (map₂ (_⊗_ o)) lhsp
        rhsp = probs' maxOdds d2
        rhs = Data.List.map (map₂ (_⊗_ (complement o))) rhsp
     in
    sumℚ (map expected (lhs ++ rhs))
  ≡⟨ cong sumℚ (map-++-commute expected lhs rhs) ⟩
    sumℚ (map expected lhs ++ map expected rhs)
  ≡⟨ cong sumℚ (cong₂ _++_ (sym (map-compose lhsp)) (sym (map-compose rhsp))) ⟩
    sumℚ (map (expected ∘ map₂ (_⊗_ o)) lhsp
       ++ map (expected ∘ map₂ (_⊗_ (complement o))) rhsp)
  ≡⟨ sumℚ-homo (map (expected ∘ map₂ (_⊗_ o)) lhsp) _ ⟩
    let rhs_now = sumℚ (map (expected ∘ map₂ (_⊗_ (complement o))) rhsp)
     in
    sumℚ (map (expected ∘ map₂ (_⊗_ o)) lhsp)
      + rhs_now
  ≡⟨⟩
    sumℚ (map (λ { (e , x) → odds→rat (o ⊗ x) * utility e }) lhsp)
      + rhs_now
  ≡⟨ ? ⟩
    sumℚ (map (λ { (e , x) → (odds→rat o * odds→rat x) * utility e }) lhsp)
      + rhs_now
  ≡⟨ ? ⟩
    o' * score d1 + (1ℚ - o') * score d2
  ∎
  where
    o' = odds→rat o
    open ≡-Reasoning

record _⊑_ (d1 d2 : Dist e) : Set where
  constructor prefers
  field
    better-score : score d1 ≤ score d2

open import pref _⊑_
open import Relation.Nullary
open import Data.Sum

bias≤ : (d1 d2 d3 : Dist e)  → (o : Odds) → score d1 ≤ score d2 → score (bias o d1 d3) ≤ score (bias o d2 d3)
bias≤ d1 d2 d3 o d1≤d2 =
  begin
    ?
  ≤⟨ ? ⟩
    ?
  ∎
  where open ≤-Reasoning

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
