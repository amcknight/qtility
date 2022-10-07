open import uniform using (Dist; mergeDist; Odds)

module pref {e : Set} (_≤_ : Dist e -> Dist e -> Set) where

open import Data.Product

record VNM : Set where
  field
    refl : (a : Dist e) -> a ≤ a
    trans : (a b c : Dist e) -> a ≤ b -> b ≤ c -> a ≤ c
    cont : (a b c : Dist e) -> a ≤ b -> b ≤ c -> Σ Odds λ o → let b' = mergeDist o a c in b' ≤ b × b' ≤ b
    indep : (a b c : Dist e) -> a ≤ b -> (o : Odds) -> mergeDist o a c ≤ mergeDist o b c
