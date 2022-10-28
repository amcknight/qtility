module utils where

open import Data.Rational
open import Data.List
open import Data.List.Properties
open import Data.Rational.Properties
open import Relation.Binary.PropositionalEquality

sumℚ : List ℚ → ℚ
sumℚ = foldr _+_ 0ℚ

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

