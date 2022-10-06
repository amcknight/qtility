{-# OPTIONS --type-in-type #-}

module stuff where

open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Fin hiding (_≤_)

record Iso (a : Set) (b : Set) : Set where
  field
    to : a -> b
    from : b -> a
    toFrom : (x : a) -> from (to x) ≡ x
    fromTo : (x : b) -> to (from x) ≡ x

≤-step : {m n : ℕ} -> m ≤ n -> m ≤ suc n
≤-step z≤n = z≤n
≤-step (s≤s x) = s≤s (≤-step x)

n≤n : {n : ℕ} -> n ≤ n
n≤n {zero} = z≤n
n≤n {suc n} = s≤s n≤n

module _ {n : ℕ} {a : Set} (isofin : Iso a (Fin (suc n))) where
  biggest : Fin (suc n)
  biggest = fromℕ n
  foldℕ : {m : ℕ} -> (m ≤ suc n) -> (i : Fin m) -> {y : Set} -> (Fin (suc n) -> y -> y) -> y -> y
  foldℕ _ zero f acc = f zero acc
  foldℕ (s≤s proof) (suc i) f acc = f (inject≤ (suc i) (s≤s proof)) (foldℕ (≤-step proof) i f acc)


data Bool : Set where
  False : Bool
  True : Bool

not : Bool -> Bool
not False = True
not True = False

data Prob : Set where
  Zero : Prob
  Top : Prob
  conj : Prob -> Prob -> Prob
  disj : Prob -> Prob -> Prob

data LTE : Prob -> Prob -> Set where
  ZeroLTE : (a : Prob) -> LTE Zero a

data Eq : Prob -> Prob -> Set where
  refl : {a : Prob} -> Eq a a
  symm : {a b : Prob} -> Eq a b -> Eq b a
  tran : {a b c : Prob} -> Eq a b -> Eq b c -> Eq a c
  conjComm : {a b : Prob} → Eq (conj a b) (conj b a) 
  disjComm : {a b : Prob} → Eq (disj a b) (disj b a)
  zeroDisj : {a : Prob} -> Eq (disj Zero a) a
  topConj : {a : Prob} -> Eq (conj Top a) a

record Gamble {n : ℕ} {a : Set} (isofin : Iso a (Fin (suc n))) (g : a -> Prob) : Set where
  field
    everything : Eq Top (foldℕ isofin (s≤s n≤n) (biggest isofin) (λ f p → disj (g (isofin .Iso.from f)) p) Zero)

data Coin : Set where
  Heads : Coin
  Tails : Coin

isoCoinFin : Iso Coin (Fin 2)
Iso.to isoCoinFin Heads = zero
Iso.to isoCoinFin Tails = suc zero
Iso.from isoCoinFin zero = Heads
Iso.from isoCoinFin (suc zero) = Tails
Iso.toFrom isoCoinFin Heads = refl
Iso.toFrom isoCoinFin Tails = refl
Iso.fromTo isoCoinFin zero = refl
Iso.fromTo isoCoinFin (suc zero) = refl

headCoin : Coin -> Prob
headCoin Heads = Top
headCoin Tails = Zero

headCoinIsGamble : Gamble isoCoinFin headCoin
Gamble.everything headCoinIsGamble = symm (tran zeroDisj (tran disjComm zeroDisj))
