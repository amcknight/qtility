{-# OPTIONS --type-in-type #-}

module uniform where

open import Data.Vec
open import Data.List hiding ([_]; map)
open import Data.Nat
open import Data.Bool hiding (_≤_)
open import Data.Nat.Properties
open import Data.Product hiding (map)
open import microproofs using (n≤n; m≤n→m≤n+k)
open import event using (Coin; Heads; Tails)

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

maxOdds : Odds
Odds.numer maxOdds = 1
Odds.denom maxOdds = 1
Odds.denom≠0 maxOdds = n≤n
Odds.numer≤denom maxOdds = n≤n

splitOdds : Odds -> (n : ℕ) -> (suc zero ≤ n) -> Odds
Odds.numer (splitOdds (odds numer denom denom≠0 numer≤denom) n n≠0) = numer
Odds.denom (splitOdds (odds numer denom denom≠0 numer≤denom) n n≠0) = n * denom
Odds.denom≠0 (splitOdds (odds numer (suc denom) denom≠0 numer≤denom) (suc n) n≠0) = s≤s z≤n
Odds.numer≤denom (splitOdds (odds numer denom denom≠0 numer≤denom) (suc n) n≠0) = m≤n→m≤n+k numer denom _ numer≤denom

{-# TERMINATING #-}
probs' : {e : Set} -> Odds -> Dist e -> List (e × Odds)
probs' o (always x) = (x , o) ∷ []
probs' o (uniform {n} x) = Data.List.concat ( toList ( map (probs' o') x ) )
  where o' = splitOdds o (suc n) (s≤s z≤n)

probs : {e : Set} -> Dist e -> List (e × Odds)
probs = probs' maxOdds

_≡_ : Set -> Set -> Bool

insertWorld : Set × Odds -> List (Set × Odds) -> List (Set × Odds)
insertWorld (e , o) [] =  (e , o) ∷ []
insertWorld (e , o) ((me , mo) ∷ mws) = if {!  e ≡ me !} then {!   !} else {!   !}

mergeWorlds' : List (Set × Odds) -> List (Set × Odds) -> List (Set × Odds)
mergeWorlds' [] mws = mws
mergeWorlds' (w ∷ ws) mws = mergeWorlds' ws (insertWorld w mws)

mergeWorlds : List (Set × Odds) -> List (Set × Odds)
mergeWorlds ws = mergeWorlds' ws []

postulate
  mergeDist : {e : Set} -> Odds -> Dist e -> Dist e -> Dist e

fairCoin : Dist Coin
fairCoin = uniform ( always Heads ∷ always Tails ∷ [] )

headBiasCoin : Dist Coin
headBiasCoin = uniform ( always Heads ∷ always Heads ∷ fairCoin ∷ [] )

run = probs headBiasCoin
 