/-
# `Qtility.Mixing` — axioms about how mixtures behave

Auxiliary structure: `MixingStructure`, `Orthogonality`.
Axioms: `CompoundReduction` (2a), `MonotoneOwnWeight` (2b),
        `OrthogonalIndependence` (2c).

These are the "independence-family" strengthenings. Classical vNM bundles
them into a single independence axiom; we keep them separable so we can
adopt the safe pieces (2c) without the unsafe ones.
-/

import Qtility.Base

namespace Qtility

universe u

/-! ## Auxiliary: `MixingStructure`

An abstract binary mixing operation on `M`. The parameter type `Param` is
chosen by the instance:

  | Instance              | `Param`                          |
  | --------------------- | -------------------------------- |
  | Classical lottery     | `ℝ` (weight in `[0,1]`)          |
  | Rebit                 | `ℝ × ℝ` with unit ℓ² norm        |
  | Qubit                 | `ℂ × ℂ` with unit ℓ² norm        |

The convention is `mix p a b` returns a mixture of `a` and `b` parameterized
by `p`; the precise semantics is instance-specific. -/

class MixingStructure (M : Type u) where
  Param : Type
  mix : Param → M → M → M

/-! ## Auxiliary: `Orthogonality`

A predicate stating that two states are "non-interfering" in the relevant
sense. Quantum: `⟨ψ | φ⟩ = 0`. Classical lottery: disjoint support. Used
by `OrthogonalIndependence` to delimit the safe zone for independence. -/

class Orthogonality (M : Type u) where
  orth : M → M → Prop

/-! ## 2a — Compound mixture reduction (schematic)

Compound mixtures should reduce to flat mixtures with combined parameters.

Classical: `λ·(μA + (1-μ)B) + (1-λ)·C  ≈  (λμ)A + (λ(1-μ))B + (1-λ)C`.

Quantum: amplitudes multiply through compound superpositions —
`α·(γψ₁ + δψ₂) + βφ  ≈  αγψ₁ + αδψ₂ + βφ`.

Stating this generically requires an algebra on `Param` (how to combine
two mixing parameters), which is itself instance-specific. We leave the
*signature* here and defer the concrete equation to each instance. -/

class CompoundReduction (M : Type u) [Preference M] [MixingStructure M] : Prop where
  /-- Schematic placeholder. Concrete reduction equation supplied per instance. -/
  reduce : True

/-! ## 2b — Monotonicity in own weight

Increasing the weight on the more-preferred component (with the other
component fixed) moves the mixture in the preferred direction.

Requires a partial order on `Param` so we can talk about "more weight". -/

class MonotoneOwnWeight (M : Type u) [Preference M] [MixingStructure M]
    (paramLE : MixingStructure.Param M → MixingStructure.Param M → Prop) : Prop where
  /-- Read `paramLE p q` as "`p` puts less weight on the first slot than `q`."
  Then increasing the weight on the strictly-preferred component `a` (with
  the other component `c` fixed) moves the mixture in the preferred direction. -/
  monotone :
    ∀ (p q : MixingStructure.Param M) (a c : M),
      paramLE p q → (c ≺ a) →
      (MixingStructure.mix p a c ≼ MixingStructure.mix q a c)

/-! ## 2c — Orthogonal independence (the "safe zone")

Classical independence in full strength fails in the quantum setting
because the "third option" can interfere with the things being compared.
This restricted version sidesteps that: independence holds when the
third option is *orthogonal* to both compared items, ruling out any
interference and recovering the classical conclusion.

This is the most plausibly-survivable piece of #2. -/

class OrthogonalIndependence
    (M : Type u) [Preference M] [MixingStructure M] [Orthogonality M] : Prop where
  preserve :
    ∀ (p : MixingStructure.Param M) (a b c : M),
      Orthogonality.orth a c → Orthogonality.orth b c → (a ≼ b) →
      (MixingStructure.mix p a c ≼ MixingStructure.mix p b c)

end Qtility
