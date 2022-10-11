{-# OPTIONS --type-in-type #-}

module uniform where

open import Data.Vec hiding (_++_)
open import Data.List hiding ([_]; map)
open import Data.Nat
open import Data.Bool hiding (_≤_)
open import Data.Nat.Properties
open import Data.Product hiding (map)
open import Relation.Binary.PropositionalEquality
open import microproofs using (n≤n; m≤n→m≤n+k)
open import event using (Coin; Heads; Tails)

record Odds : Set where
  constructor odds
  field
    numer : ℕ
    denom : ℕ
    denom≠0 : suc zero ≤ denom
    numer≤denom : numer ≤ denom

data Dist (e : Set) : Set where
  always : e -> Dist e
  uniform : {n : ℕ} -> Vec (Dist e) (suc n) -> Dist e
  bias : Odds -> Dist e -> Dist e -> Dist e


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

_⊗_ : Odds -> Odds -> Odds
odds n1 d1 (s≤s denom≠0) numer≤denom ⊗ odds n2 d2 (s≤s denom≠0₁) numer≤denom₁ = odds (n1 * n2) (d1 * d2) (s≤s z≤n) (*-mono-≤ numer≤denom numer≤denom₁)

d∸n≤d : (d : ℕ) -> (n : ℕ) -> d ∸ n ≤ d
d∸n≤d zero zero = z≤n
d∸n≤d zero (suc n) = z≤n
d∸n≤d (suc d) zero = s≤s n≤n
d∸n≤d (suc d) (suc n) = ≤-trans (d∸n≤d d n) (≤-step n≤n)

complement : Odds -> Odds
complement (odds numer denom denom≠0 numer≤denom) = odds (denom ∸ numer) denom denom≠0 (d∸n≤d denom numer)

uip : {a : Set} -> {x y : a} -> (p q : x ≡ y) -> (p ≡ q)
uip refl refl = refl

-- compcompid : (o : Odds) -> o ≡ complement (complement o)
-- compcompid o = {!   !}

{-# TERMINATING #-}
probs' : {e : Set} -> Odds -> Dist e -> List (e × Odds)
probs' o (always x) = (x , o) ∷ []
probs' o (uniform {n} x) = Data.List.concat ( toList ( map (probs' o') x ) )
  where o' = splitOdds o (suc n) (s≤s z≤n)
probs' o (bias o' a b) = Data.List.map (map₂ (_⊗_ o')) (probs' o a) ++ Data.List.map (map₂ (_⊗_ (complement o'))) (probs' o b)

probs : {e : Set} -> Dist e -> List (e × Odds)
probs = probs' maxOdds

-- _≡_ : Set -> Set -> Bool

-- insertWorld : Set × Odds -> List (Set × Odds) -> List (Set × Odds)
-- insertWorld (e , o) [] =  (e , o) ∷ []
-- insertWorld (e , o) ((me , mo) ∷ mws) = if {!  e ≡ me !} then {!   !} else {!   !}

-- mergeWorlds' : List (Set × Odds) -> List (Set × Odds) -> List (Set × Odds)
-- mergeWorlds' [] mws = mws
-- mergeWorlds' (w ∷ ws) mws = mergeWorlds' ws (insertWorld w mws)

-- mergeWorlds : List (Set × Odds) -> List (Set × Odds)
-- mergeWorlds ws = mergeWorlds' ws []

fairCoin : Dist Coin
fairCoin = uniform ( always Heads ∷ always Tails ∷ [] )

headBiasCoin : Dist Coin
headBiasCoin = uniform ( always Heads ∷ always Heads ∷ fairCoin ∷ [] )

run = probs headBiasCoin
 