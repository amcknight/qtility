{-# OPTIONS --type-in-type #-}

module uniform where

open import Data.Vec hiding (_++_)
open import Data.List hiding ([_]; map)
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Bool hiding (_≤_)
open import Data.Nat.Properties
open import Data.Product hiding (map)
open import Relation.Binary.PropositionalEquality
open import microproofs using (n≤n; m≤n→m≤n+k)
open import event using (Coin; Heads; Tails)
open import Data.Rational
import Data.Rational.Properties as ℚ-Properties
import Data.Integer as ℤ
import Data.Integer.Properties
open import Data.Rational.Unnormalised.Base as ℚᵘ using (_≢0)

record Odds : Set where
  constructor odds
  field
    value : ℚ
    is-pos : ℤ.0ℤ ℤ.≤ ↥ value
    is-odds : ℤ.∣ ↥ value ∣ ℕ.≤ ↧ₙ value

data Dist (e : Set) : Set where
  always : e -> Dist e
  uniform : {n : ℕ} -> Vec (Dist e) (suc n) -> Dist e
  bias : Odds -> Dist e -> Dist e -> Dist e

open import Data.Unit using (tt)

maxOdds : Odds
Odds.value maxOdds = 1ℚ
Odds.is-pos maxOdds = ℤ.+≤+ ℕ.z≤n
Odds.is-odds maxOdds = ℕ.s≤s ℕ.z≤n

build-≢0 : (n : ℕ) → (0 ℕ.< n) → n ≢0
build-≢0 .(suc _) (ℕ.s≤s x) = tt

build-eq≢0 : (n : ℕ) → (0 ≢ n) → n ≢0
build-eq≢0 zero x = x refl
build-eq≢0 (suc n) x = tt

fromNat : ℕ → ℚ
fromNat n = normalize n 1

-- ↥-normalize : ∀ i n {n≢0} → ↥ (normalize i n {n≢0}) ℤ.* gcd (+ i) (+ n) ≡ + i

open import Data.Integer.GCD using (gcd)
import Data.Nat.GCD

open import Data.Sum using (inj₂)
open import Data.Empty

lemma : ∀ n → (n ≢ 0) → (n ℕ.≤ 1) → n ≡ 1
lemma .zero x ℕ.z≤n = ⊥-elim (x refl)
lemma .1 x (ℕ.s≤s ℕ.z≤n) = refl

gcd-yo : ∀ n → gcd (ℤ.+ n) (ℤ.+ 1) ≡ ℤ.+ 1
gcd-yo n with Data.Nat.GCD.gcd[m,n]≤n n 0 | Data.Nat.GCD.gcd[m,n]≢0 n 1 (inj₂ λ { () })
... | gcd≤1 | gcd≠0 rewrite lemma _ gcd≠0 gcd≤1 = refl

yo' : ∀ n → n ≡ ℤ.∣ ↥ fromNat n ∣
yo' n =
  begin
    n                                                ≡⟨⟩
    ℤ.∣ ℤ.+ n ∣                                      ≡⟨ sym (cong ℤ.∣_∣ (ℚ-Properties.↥-normalize n 1)) ⟩
    ℤ.∣ ↥ (normalize n 1) ℤ.* gcd (ℤ.+ n) (ℤ.+ 1) ∣  ≡⟨ cong (\ φ → ℤ.∣ ↥ (normalize n 1) ℤ.* φ ∣) (gcd-yo n) ⟩
    ℤ.∣ ↥ (normalize n 1) ℤ.* ℤ.1ℤ ∣                 ≡⟨ cong ℤ.∣_∣ (Data.Integer.Properties.*-identityʳ (↥ normalize n 1)) ⟩
    ℤ.∣ ↥ (normalize n 1) ∣                          ≡⟨⟩
    ℤ.∣ ↥ fromNat n ∣                                ∎
  where open ≡-Reasoning


splitOdds : Odds → (n : ℕ) → (0 ℕ.< n) → Odds
Odds.value (splitOdds x n 0<n) = Odds.value x * 1/_ (fromNat n) { build-≢0 ℤ.∣ ↥ fromNat n ∣ (≤-trans 0<n (Data.Nat.Properties.≤-reflexive (yo' n))) }
Odds.is-pos (splitOdds x n 0<n) = {! !}
Odds.is-odds (splitOdds x n 0<n) = {! !}
-- Odds.numer (splitOdds (odds numer denom denom≠0 numer≤denom) n n≠0) = numer
-- Odds.denom (splitOdds (odds numer denom denom≠0 numer≤denom) n n≠0) = n * denom
-- Odds.denom≠0 (splitOdds (odds numer (suc denom) denom≠0 numer≤denom) (suc n) n≠0) = s≤s z≤n
-- Odds.numer≤denom (splitOdds (odds numer denom denom≠0 numer≤denom) (suc n) n≠0) = m≤n→m≤n+k numer denom _ numer≤denom

_⊗_ : Odds -> Odds -> Odds
_⊗_ = ?
-- odds n1 d1 (s≤s denom≠0) numer≤denom ⊗ odds n2 d2 (s≤s denom≠0₁) numer≤denom₁ = odds (n1 * n2) (d1 * d2) (s≤s z≤n) (*-mono-≤ numer≤denom numer≤denom₁)

-- d∸n≤d : (d : ℕ) -> (n : ℕ) -> d ℕ.∸ n ≤ d
-- d∸n≤d zero zero = z≤n
-- d∸n≤d zero (suc n) = z≤n
-- d∸n≤d (suc d) zero = s≤s n≤n
-- d∸n≤d (suc d) (suc n) = ≤-trans (d∸n≤d d n) (≤-step n≤n)

-- complement : Odds -> Odds
-- complement (odds numer denom denom≠0 numer≤denom) = odds (denom ∸ numer) denom denom≠0 (d∸n≤d denom numer)

-- uip : {a : Set} -> {x y : a} -> (p q : x ≡ y) -> (p ≡ q)
-- uip refl refl = refl

-- -- compcompid : (o : Odds) -> o ≡ complement (complement o)
-- -- compcompid o = {!   !}

-- {-# TERMINATING #-}
-- probs' : {e : Set} -> Odds -> Dist e -> List (e × Odds)
-- probs' o (always x) = (x , o) ∷ []
-- probs' o (uniform {n} x) = Data.List.concat ( toList ( map (probs' o') x ) )
--   where o' = splitOdds o (suc n) (s≤s z≤n)
-- probs' o (bias o' a b) = Data.List.map (map₂ (_⊗_ o')) (probs' o a) ++ Data.List.map (map₂ (_⊗_ (complement o'))) (probs' o b)

-- probs : {e : Set} -> Dist e -> List (e × Odds)
-- probs = probs' maxOdds

-- -- _≡_ : Set -> Set -> Bool

-- -- insertWorld : Set × Odds -> List (Set × Odds) -> List (Set × Odds)
-- -- insertWorld (e , o) [] =  (e , o) ∷ []
-- -- insertWorld (e , o) ((me , mo) ∷ mws) = if {!  e ≡ me !} then {!   !} else {!   !}

-- -- mergeWorlds' : List (Set × Odds) -> List (Set × Odds) -> List (Set × Odds)
-- -- mergeWorlds' [] mws = mws
-- -- mergeWorlds' (w ∷ ws) mws = mergeWorlds' ws (insertWorld w mws)

-- -- mergeWorlds : List (Set × Odds) -> List (Set × Odds)
-- -- mergeWorlds ws = mergeWorlds' ws []

-- fairCoin : Dist Coin
-- fairCoin = uniform ( always Heads ∷ always Tails ∷ [] )

-- headBiasCoin : Dist Coin
-- headBiasCoin = uniform ( always Heads ∷ always Heads ∷ fairCoin ∷ [] )

-- run = probs headBiasCoin

