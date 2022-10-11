module microproofs where

open import Data.Nat
open import Data.Nat.Properties hiding (≤-step)
open import Relation.Binary.PropositionalEquality

≤-step : {m n : ℕ} -> m ≤ n -> m ≤ suc n
≤-step z≤n = z≤n
≤-step (s≤s x) = s≤s (≤-step x)

n≤n : {n : ℕ} -> n ≤ n
n≤n {zero} = z≤n
n≤n {suc n} = s≤s n≤n

m≤n→m≤n+k : (m n k : ℕ) -> m ≤ n -> m ≤ n + k
m≤n→m≤n+k zero n k m≤n = z≤n
m≤n→m≤n+k (suc m) (suc n) k (s≤s m≤n) = s≤s (m≤n→m≤n+k m n k m≤n)

-- 2*a = a + a
f : (a : ℕ) -> 2 * a ≡ a + a
f a = begin
    2 * a
  ≡⟨⟩
    a + (a + zero)
  ≡⟨ +-comm a (a + zero) ⟩
    (a + zero) + a
  ≡⟨ cong (_+ a) (+-comm a zero) ⟩
    a + a
  ∎
  where open ≡-Reasoning