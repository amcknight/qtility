{-# OPTIONS --type-in-type #-}

module uniform where

open import Data.Vec
open import Data.List hiding ([_])
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import stuff using (n≤n; Coin; Heads; Tails)

data Dist (e : Set) : Set where
  always : e -> Dist e
  uniform : {n : ℕ} -> Vec (Dist e) (suc n) -> Dist e

record Odds : Set where
  constructor odds
  field
    numer : ℕ
    denom : ℕ
    denom≠0 : suc zero ≤ denom
    numer≤denom : numer ≤ denom

maxProb100% : Odds
Odds.numer maxProb100% = 1
Odds.denom maxProb100% = 1
Odds.denom≠0 maxProb100% = n≤n
Odds.numer≤denom maxProb100% = n≤n

m≤n→m≤n+k : (m n k : ℕ) -> m ≤ n -> m ≤ n + k
m≤n→m≤n+k zero n k m≤n = z≤n
m≤n→m≤n+k (suc m) (suc n) k (s≤s m≤n) = s≤s (m≤n→m≤n+k m n k m≤n)

splitOdds : Odds -> (n : ℕ) -> (suc zero ≤ n) -> Odds
Odds.numer (splitOdds (odds numer denom denom≠0 numer≤denom) n n≠0) = numer
Odds.denom (splitOdds (odds numer denom denom≠0 numer≤denom) n n≠0) = n * denom
Odds.denom≠0 (splitOdds (odds numer (suc denom) denom≠0 numer≤denom) (suc n) n≠0) = s≤s z≤n
Odds.numer≤denom (splitOdds (odds numer denom denom≠0 numer≤denom) (suc n) n≠0) = m≤n→m≤n+k numer denom _ numer≤denom

{-# TERMINATING #-}
probs : {e : Set} -> Odds -> Dist e -> List (e × Odds)
probs o (always x) = (x , o) ∷ []
probs o (uniform {n} x) = Data.List.concat ( Data.Vec.toList ( Data.Vec.map (probs o') x ) )
  where o' = splitOdds o (suc n) (s≤s z≤n)

postulate
  mergeDist : {e : Set} -> Odds -> Dist e -> Dist e -> Dist e

fairCoin : Dist Coin
fairCoin = uniform ( always Heads ∷ always Tails ∷ [] )

headBiasCoin : Dist Coin
headBiasCoin = uniform ( always Heads ∷ always Heads ∷ fairCoin ∷ [] )

getProbs : _
getProbs = probs maxProb100% headBiasCoin
