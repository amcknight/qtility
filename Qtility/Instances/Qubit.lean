/-
# `Qtility.Instances.Qubit` — qubit density matrices

State space: density matrices on `ℂ²` (Hermitian, positive-semidefinite,
trace-1 complex 2×2 matrices). Defined for general `n` as `DensityMatrix n`;
`Qubit` is the `n = 2` specialization.

Preference family: `(Tr(Ô · ρ)).re` ordering induced by a Hermitian
observable `Ô`.

This is the **target #1** instance — the natural quantum analog of the
classical EU lottery, with utility encoded by an observable rather than
a scalar function.

## Status

Type-level scaffolding only. The basic structure types and the EU-like
preference compile. Many axiom verifications are deferred — see the
"What's missing" comment at the end.
-/

import Qtility.Base
import Qtility.Mixing
import Qtility.PhysicalAxioms
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace

open Qtility

namespace Qtility.Instances

/-! ## The state space -/

/-- A finite-dimensional density matrix on `ℂⁿ`: Hermitian, (PSD,) trace 1.

⚠ TODO: also require positive-semidefinite. `Matrix.PosSemidef` on a
`ℂ`-matrix needs `RCLike`-mediated machinery from
`Mathlib.LinearAlgebra.Matrix.PosDef` plus a `PartialOrder ℂ` setup we
haven't wired up yet. For now we leave PSD out of the structure with the
understanding that downstream proofs will need to assume it explicitly
(or we'll add it when we get to representation-theorem proof). -/
structure DensityMatrix (n : ℕ) where
  /-- The underlying complex matrix. -/
  M : Matrix (Fin n) (Fin n) ℂ
  /-- Hermitian: `M = M†`. -/
  hermitian : M.IsHermitian
  /-- Trace 1 (normalization). -/
  trace_one : M.trace = 1

/-- A qubit density matrix. -/
abbrev Qubit := DensityMatrix 2

namespace DensityMatrix

variable {n : ℕ}

/-! ## Observable-expectation preference

For a fixed Hermitian observable `Ô`, preferences order density matrices
by the real part of `Tr(Ô · ρ)`. -/

/-- The expectation value `Tr(Ô · ρ)` — generally complex; real when `Ô`
is Hermitian. -/
def expectation (Ô : Matrix (Fin n) (Fin n) ℂ) (ρ : DensityMatrix n) : ℂ :=
  (Ô * ρ.M).trace

/-- The observable-induced preference relation. -/
@[reducible]
def ObservablePref (Ô : Matrix (Fin n) (Fin n) ℂ) :
    Preference (DensityMatrix n) where
  pref ρ σ := (expectation Ô ρ).re ≤ (expectation Ô σ).re

/-! ## Axiom verifications -/

instance ObservablePref_isReflexive (Ô : Matrix (Fin n) (Fin n) ℂ) :
    letI : Preference (DensityMatrix n) := ObservablePref Ô
    IsReflexive (DensityMatrix n) :=
  letI : Preference (DensityMatrix n) := ObservablePref Ô
  ⟨fun _ => le_refl _⟩

instance ObservablePref_isTransitive (Ô : Matrix (Fin n) (Fin n) ℂ) :
    letI : Preference (DensityMatrix n) := ObservablePref Ô
    IsTransitive (DensityMatrix n) :=
  letI : Preference (DensityMatrix n) := ObservablePref Ô
  ⟨fun h₁ h₂ => le_trans h₁ h₂⟩

/-! ## What's missing (deferred)

These are tractable but need more matrix-algebra setup:

* `HasClosedGraph` — topology on `DensityMatrix n` (inherit from matrix
  entries) + continuity of `Tr(Ô · ·)`
* `RespectsOperationalEquivalence` (B1) — define `opEquiv` as "equal `M`"
  then preferences factor through trivially (they're already a function
  of `ρ.M`)
* `OrthogonalIndependence` (2c) — needs `MixingStructure` instance
  (convex combination of density matrices) + an `Orthogonality` predicate
  (orthogonal supports). Linearity of trace gives the result.
* `IsInvariantUnder` for the global phase action — global phase `ψ → e^{iθ}ψ`
  lifts to density matrices as `ρ → ρ` (already trivial at the density
  matrix level — this is *why* preferences live on density matrices)

The interesting axioms (`MonotoneInCoherence` (C1), `NoMeasurePump` (NMP),
`AncillaInvariant` (R1)) constrain *which* `Ô` is allowed — they
correspond to physical conditions on the utility observable.
-/

end DensityMatrix
end Qtility.Instances
