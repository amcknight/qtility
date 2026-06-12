/-
# `Qtility.Symmetry` — basis-level symmetry axioms

Axioms about how preferences interact with group actions that permute or
phase-rotate basis states (as opposed to the global phase action in
`Base.IsInvariantUnder`).

Contents: `PermutationInvariant` (4a), `PerOutcomePhaseInvariant` (4c).

⚠ **Mutual-exclusion warning.** Adopting both 4a and 4c collapses the
theory back to symmetric functions of the Born distribution `{|αᵢ|²}` —
i.e., back to classical lottery preferences. Adopt **at most one** in
any given run.
-/

import Qtility.Base
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Perm.Basic

namespace Qtility

universe u

/-! ## 4a — Permutation invariance ⚠

Invariance under permutations of basis labels (`S_n` action).

Classical analog: "anonymity over outcomes" — apple vs orange labels don't
matter, only the probabilities.

Quantum: keeps phase structure intact (because permutations are unitary
but only act on indices, not on amplitudes' phases) — so it's not the
classical-trapdoor on its own.

⚠ Combining with `PerOutcomePhaseInvariant` (4c) trivializes — see file
header. Use at most one. -/

class PermutationInvariant
    (M : Type u) (n : ℕ) [Preference M] [MulAction (Equiv.Perm (Fin n)) M] : Prop where
  invariant : ∀ (σ : Equiv.Perm (Fin n)) (a b : M),
    (σ • a ≼ σ • b) ↔ (a ≼ b)

/-! ## 4c — Per-outcome phase invariance ⚠

Preferences invariant under independent phase rotations of each
basis-state amplitude. For a qubit this is `U(1)^n` acting coordinatewise
on the amplitudes; for a rebit it's `{-1, +1}^n` (sign flips).

Stronger than the global phase invariance in `IsInvariantUnder` — that
forces only `(e^{iθ}, e^{iθ}, ...)` invariance; this forces invariance
under `(e^{iθ₁}, e^{iθ₂}, ...)` for *independent* `θᵢ`.

⚠ Combining with `PermutationInvariant` (4a) trivializes — see file
header. Use at most one. -/

/-- The `phaseAction` parameter is instance-supplied: it's the action of
an `n`-tuple of phase parameters on `M`. The phase-parameter type is
modeled here as `Fin n → ℝ` for generality; concrete instances will
restrict (e.g. `Fin n → Circle` for qubits via amplitude rotation). -/
class PerOutcomePhaseInvariant
    (M : Type u) (n : ℕ) [Preference M]
    (phaseAction : (Fin n → ℝ) → M → M) : Prop where
  invariant : ∀ (θ : Fin n → ℝ) (a b : M),
    (phaseAction θ a ≼ phaseAction θ b) ↔ (a ≼ b)

end Qtility
