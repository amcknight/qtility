/-
# `Qtility.Instances.Lottery` — classical finite lotteries

State space: discrete probability distributions over `Fin n`.

Preference family: expected utility induced by a utility function
`u : Fin n → ℝ` on outcomes.

Sanity-check instance: shows that our axiom toolkit reproduces classical
vNM expected utility when applied to the classical state space.

## Axioms verified

* `IsReflexive`, `IsTransitive`           floor — trivial via `≤` on ℝ

## Axioms left as TODO (next pass)

* `HasClosedGraph`, `HasClosedIndifference`   needs induced topology argument
* `IsInvariantUnder Unit`                      trivial classical case;
                                               skipped while we sort out group
                                               instance imports
* `MonotoneOwnWeight` (2b), `OrthogonalIndependence` (2c)
                                              should hold; matrix algebra
* `CompoundReduction` (2a)                    schematic; concrete `λμ` rule
-/

import Qtility.Base
import Qtility.Mixing
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Constructions

open Qtility

namespace Qtility.Instances

/-! ## The state space -/

/-- A classical lottery over `n` outcomes: a probability distribution on `Fin n`. -/
@[ext]
structure Lottery (n : ℕ) where
  /-- The probability assigned to each outcome. -/
  probs : Fin n → ℝ
  /-- Each probability is non-negative. -/
  nonneg : ∀ i, 0 ≤ probs i
  /-- Probabilities sum to 1. -/
  sum_one : (Finset.univ : Finset (Fin n)).sum probs = 1

namespace Lottery

variable {n : ℕ}

/-- Lotteries inherit the topology from the underlying probability vector. -/
instance : TopologicalSpace (Lottery n) :=
  TopologicalSpace.induced Lottery.probs inferInstance

/-! ## The expected-utility preference family

For a fixed utility function `u : Fin n → ℝ` on outcomes, the EU-induced
preference on lotteries is the `≤` ordering on expected utilities. -/

/-- Expected utility of a lottery under a given outcome-utility. -/
def EU (u : Fin n → ℝ) (p : Lottery n) : ℝ :=
  (Finset.univ : Finset (Fin n)).sum (fun i => p.probs i * u i)

/-- The expected-utility preference relation induced by a utility on outcomes.

Marked `@[reducible]` so that the underlying `Preference` typeclass field
unfolds during typeclass inference — needed for the axiom-verification
instances below to typecheck. -/
@[reducible]
def EUPref (u : Fin n → ℝ) : Preference (Lottery n) where
  pref p q := EU u p ≤ EU u q

/-! ## Axiom verifications

Each instance below confirms that `(Lottery n, EUPref u)` inhabits the
corresponding axiom typeclass. Use these by `letI := EUPref u` to bring
the preference into scope. -/

/-- EU preference is reflexive. -/
instance EUPref_isReflexive (u : Fin n → ℝ) :
    letI : Preference (Lottery n) := EUPref u
    IsReflexive (Lottery n) :=
  letI : Preference (Lottery n) := EUPref u
  ⟨fun _ => le_refl _⟩

/-- EU preference is transitive. -/
instance EUPref_isTransitive (u : Fin n → ℝ) :
    letI : Preference (Lottery n) := EUPref u
    IsTransitive (Lottery n) :=
  letI : Preference (Lottery n) := EUPref u
  ⟨fun h₁ h₂ => le_trans h₁ h₂⟩

end Lottery
end Qtility.Instances
