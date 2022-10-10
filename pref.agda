open import uniform using (Dist; mergeDist; Odds)

module pref {e : Set} (_≤_ : Dist e -> Dist e -> Set) where

open import Data.Product
open import Data.Sum

record VNM : Set where
  field
    refl : (a : Dist e) -> a ≤ a
    comp : (a b : Dist e) -> a ≤ b ⊎ b ≤ a
    trans : (a b c : Dist e) -> a ≤ b -> b ≤ c -> a ≤ c
    cont : (a b c : Dist e) -> a ≤ b -> b ≤ c -> Σ Odds λ o → let b' = mergeDist o a c in b' ≤ b × b ≤ b'
    indep : (a b c : Dist e) -> a ≤ b -> (o : Odds) -> mergeDist o a c ≤ mergeDist o b c

-- module X (vnm : VNM) where 
--   open VNM vnm
--   open import Data.List
  
--   postulate
--     allEs : List e
--     best : Dist e
--     bestIsBest : (d : Dist e) -> d ≤ best
--     worst : Dist e
--     worstIsWorst : (d : Dist e) -> worst ≤ d
    

  -- utility : e -> Odds
  -- utility = {!  !}


--  pickU utility d1 d2 = probs(d1) . utility(events(d1)) > probs(d2) . utility(events(d2))
