open import Data.Rational

module utility.score {e : Set} (utility : e -> ℚ) where

open import Function using (_∘_)
open import uniform
open import utils
open import Data.Integer using (+_; -[1+_]; ℤ; 0ℤ)
open import Data.List
open import Data.List.Properties
open import Data.Product hiding (map)
import Data.Nat.Properties
open import Data.Nat using (suc; s≤s; z≤n; ℕ)
open import Data.Rational.Properties
open import Relation.Binary.PropositionalEquality
open import Data.Rational.Unnormalised.Base using (_≢0)
open import Data.Unit using (tt)
import Data.Nat as ℕ
import Data.Integer as ℤ
open import Data.Rational.Unnormalised.Base as ℚᵘ using (ℚᵘ; mkℚᵘ; _≢0)

postulate
  todo : {A : Set} → A

odds→rat : Odds -> ℚ
odds→rat (odds numer denom denom≠0 numer≤denom) = _/_ (+ numer) denom { build-≢0 denom denom≠0 }

expected : e × Odds → ℚ
expected (e , o) = odds→rat o * utility e

score : Dist e -> ℚ
score x = sumℚ (map expected (probs x))

/-distrib-*
  : ∀ p q
  → (↥ p ℤ.* ↥ q) / (↧ₙ p ℕ.* ↧ₙ q) ≡ (↥ p / ↧ₙ p) * ( ↥ q / ↧ₙ q)
/-distrib-* p q =
  begin
    (↥ p ℤ.* ↥ q) / (↧ₙ p ℕ.* ↧ₙ q)  ≡⟨⟩
    p * q                            ≡⟨ sym (cong₂ _*_ (↥p/↧p≡p p) (↥p/↧p≡p q)) ⟩
    (↥ p / ↧ₙ p) * ( ↥ q / ↧ₙ q)     ∎
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
    (+ (an Data.Nat.* bn)) / (ad Data.Nat.* bd)  ≡⟨ {! /-distrib-* (+ an / ad) (+ bn / bd) !} ⟩
    (+ an / ad) * (+ bn / bd)                    ≡⟨⟩
    odds→rat a * odds→rat b                      ∎
  where open ≡-Reasoning
