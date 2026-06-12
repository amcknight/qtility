/-
# `Qtility.PhysicalAxioms` — physics-grounded axioms

Each axiom in this file is motivated by a specific thought experiment or
physical principle rather than a pure mathematical move. They tend to be
the most empirically defensible additions but also the most "load-bearing"
once adopted — they bring real physical structure (density matrices,
coherence measures, decoherence, subsystem decomposition) into the
preference framework.

Contents:
  * `OperationalEquivalence`              auxiliary — "indistinguishable
                                          by any measurement on the
                                          scoped system"
  * `RespectsOperationalEquivalence` (B1) Bell / operationalism
  * `PostDecoherenceClassical` (E2)       Everett / Wallace, post-measurement
  * `HasMeasure`                          auxiliary — a quantity to be
                                          conserved against pumping
  * `NoMeasurePumpWeak`,                  sign-aware Dutch book: shrinking
    `NoMeasurePumpStrict` (NMP)           measure moves you toward `null`
  * `MeasureIndifference`                 the renormalizer's stance — only
                                          the ray matters
  * `NullIsWorst`                         explicit preference floor (the
                                          honest route to PSD `Ô`)
  * `MonotoneInCoherence` (C1)            Mach–Zehnder Dutch book
  * `AncillaInvariant` (R1)               environmental-unitary invariance
                                          / quantum erasure
-/

import Qtility.Base
import Mathlib.Data.Real.Basic

namespace Qtility

universe u

/-! ## Auxiliary: `OperationalEquivalence`

A predicate stating that two states are operationally indistinguishable —
no measurement on the scoped system can tell them apart. Concretely, for
quantum states scoped over system `S`, this is "same density matrix on
`S`."

Scope matters: the agent's preferences live on whatever system they care
about. Widening that system (e.g. `Alice ⊗ Bob`) widens the set of
distinguishing measurements, so fewer states are deemed equivalent.

The relation is provided by the instance. The intent is reflexive,
symmetric, and transitive (a genuine equivalence relation) but we don't
demand that structurally — Lean leaves the burden of faithfulness to the
instance. -/

class OperationalEquivalence (M : Type u) where
  opEquiv : M → M → Prop

/-! ## B1 — Respects operational equivalence

If two states are operationally indistinguishable (`opEquiv a b`), the
agent must be indifferent between them.

This rules out preferences over physically-fictitious distinctions like
global phase, or two distinct vectors yielding the same density matrix.
It does **not** rule out preferences over other people or other systems
— widening the scoped system widens the equivalence relation. -/

class RespectsOperationalEquivalence (M : Type u) [Preference M] [OperationalEquivalence M] : Prop where
  respects : ∀ a b : M, OperationalEquivalence.opEquiv a b → (a ≈ b)

/-! ## E2 — Post-decoherence classical agreement

For states that are *already classical mixtures* (diagonal in some
preferred basis), preferences should agree with the obvious classical
lottery preference over those outcomes.

This is the post-decoherence-only half of the Deutsch–Wallace branch
aggregation argument. **The pre-decoherence half** — claiming that a
coherent superposition is indifferent to its post-measurement classical
mixture — is what reduces the theory back to classical vNM via the Born
rule, and is **NOT** included here. We split E1 (full) from E2 (post-only)
deliberately; only E2 is on the shelf.

Parameterized by:
  * `isClassical : M → Prop`        which states count as "already decohered"
  * `classicalLE : M → M → Prop`    the induced classical preference on
                                    classical states (typically EU over
                                    the diagonal probabilities)
-/

class PostDecoherenceClassical (M : Type u) [Preference M]
    (isClassical : M → Prop)
    (classicalLE : M → M → Prop) : Prop where
  agrees : ∀ a b : M, isClassical a → isClassical b →
    ((a ≼ b) ↔ classicalLE a b)

/-! ## Auxiliary: `HasMeasure`

A real-valued "measure" or "stake" function on states. For classical
lotteries, the total probability (always 1 if normalized). For quantum,
the squared ℓ² norm (always 1 if normalized; less than 1 for sub-
normalized states arising from post-selection or measurement failure).

The intent is that `measure` is monotone-non-increasing under the
operations the agent has access to — `NoMeasurePump` (below) prevents
the agent from being slowly drained along this axis *on branches the
agent wants to keep*, while permitting (indeed welcoming) measure loss
on branches below the null reference. -/

class HasMeasure (M : Type u) where
  measure : M → ℝ

/-! ## NMP-weak — No measure pump (weak, sign-aware)

Shrinking measure moves a state weakly *toward* a designated `null` state
(the zero-measure / empty reference) in the preference order. Among
otherwise-equivalent states:

  * if the branch is at least as good as `null`, less measure is weakly
    worse — the classic anti-pump direction;
  * if the branch is at most as good as `null`, less measure is weakly
    *better* — losing measure on a branch you disprefer to nothing is an
    improvement, and no adversary can pump you on a state you'd pay to lose.

An earlier sign-blind form ("more measure is always weakly preferred")
secretly forbade below-null branches: under the linear trace extension to
subnormalized states it forces `Tr(ρÔ) ≥ 0` everywhere, i.e. PSD `Ô`. The
Dutch-book motivation only operates on branches the agent wants to keep, so
positivity was an artifact of the axiom, not a discovery. If a floor is
wanted, adopt `NullIsWorst` (below) explicitly.

Consequence of the two clauses together: a branch indifferent to `null` is
measure-indifferent (both clauses fire, giving `a ≈ b`).

Note: under the linear trace extension this axiom is satisfied by *every*
Hermitian observable — it constrains how preferences extend from the
normalized slice to the subnormalized cone, not the observable itself.

The `otherwiseEquivalent` predicate is supplied by the instance. For
classical lotteries it might be "same renormalized distribution shape;"
for quantum, "same density matrix up to positive scalar" (same ray). -/

class NoMeasurePumpWeak (M : Type u) [Preference M] [HasMeasure M]
    (otherwiseEquivalent : M → M → Prop) (null : M) : Prop where
  shrinkAboveNull :
    ∀ a b : M,
      otherwiseEquivalent a b →
      (null ≼ b) →
      HasMeasure.measure a < HasMeasure.measure b →
      (a ≼ b)
  shrinkBelowNull :
    ∀ a b : M,
      otherwiseEquivalent a b →
      (b ≼ null) →
      HasMeasure.measure a < HasMeasure.measure b →
      (b ≼ a)

/-! ## NMP-strict — No measure pump (strict, sign-aware)

The strict form: shrinking measure on a *strictly* above-null branch is
strictly worse; on a strictly below-null branch, strictly better. The
hypotheses use strict standing (`null ≺ b`, `b ≺ null`) — a branch
indifferent to `null` supports no strict conclusion in either direction.

Adopt only if the toolkit experiment actually needs the strict form;
otherwise `NoMeasurePumpWeak` is the more defensible default. -/

class NoMeasurePumpStrict (M : Type u) [Preference M] [HasMeasure M]
    (otherwiseEquivalent : M → M → Prop) (null : M) : Prop where
  shrinkAboveNull :
    ∀ a b : M,
      otherwiseEquivalent a b →
      (null ≺ b) →
      HasMeasure.measure a < HasMeasure.measure b →
      (a ≺ b)
  shrinkBelowNull :
    ∀ a b : M,
      otherwiseEquivalent a b →
      (b ≺ null) →
      HasMeasure.measure a < HasMeasure.measure b →
      (b ≺ a)

/-! ## Measure indifference — the renormalizer's stance

The agent intends to renormalize / condition downstream, so only the ray
(the renormalized state) carries preference; measure is bookkeeping to be
cancelled. Otherwise-equivalent states are indifferent regardless of
measure. Needs no `HasMeasure` — the stance is precisely that measure is
irrelevant.

Coherent iff renormalization / post-selection is genuinely free. If
conditioning on survival costs resources the agent values (ancillas,
erasure work), the adversary's pump closes: the agent trades down measure
"indifferently" until no resources remain to do the conditioning. Adopting
this axiom is a physical commitment about free post-selection, not a
mathematical convenience.

Mutually exclusive with `NoMeasurePumpStrict` (on any pair with strict
standing); consistent with `NoMeasurePumpWeak` only in degenerate cases. -/

class MeasureIndifference (M : Type u) [Preference M]
    (otherwiseEquivalent : M → M → Prop) : Prop where
  indifferent : ∀ a b : M, otherwiseEquivalent a b → (a ≈ b)

/-! ## Null-is-worst — explicit preference floor

The `null` state (zero measure, "nothing survives") is weakly the worst
state. This is the honest version of what the sign-blind measure-pump
axiom smuggled in: under the linear trace representation it yields
`Tr(ρÔ) ≥ 0` for all states, i.e. `Ô` positive semidefinite — the
"utility observable has a lower bound / vacuum exists" conclusion (TH05).

Adopt it when a floor is *wanted as physics*, e.g. on Landauer-style
grounds (see A05); do not expect it to fall out of pump arguments. -/

class NullIsWorst (M : Type u) [Preference M] (null : M) : Prop where
  worst : ∀ a : M, null ≼ a

/-! ## C1 — Monotone in coherence

Motivated by the Mach–Zehnder Dutch book: if preferences are non-monotonic
in coherence (e.g. you prefer "medium coherence" to both "full" and
"none"), an adversary controlling a tunable interferometer can drain you.
So preference must be monotone in some coherence measure.

The `moreCoherent` preorder is supplied by the instance — could be the
ℓ₁-norm of off-diagonal density-matrix entries, the relative entropy of
coherence, robustness of coherence, etc. The axiom is agnostic about
which measure; it just demands monotonicity. -/

/-- The `moreCoherent` parameter is instance-supplied; read `moreCoherent a b`
as "`a` has at least as much coherence as `b`, in all other respects equal." -/
class MonotoneInCoherence (M : Type u) [Preference M]
    (moreCoherent : M → M → Prop) : Prop where
  monotone : ∀ a b : M, moreCoherent a b → (b ≼ a)

/-! ## R1 — Ancilla / environmental unitary invariance

The state space decomposes (conceptually) into a "system" the agent
values and an "environment / ancilla" the agent doesn't. Unitaries
acting *only on the environment* should not change preferences.

This is strictly weaker than full unitary invariance (which trivializes)
because the action group `E` is restricted to environment-only unitaries.
The faithfulness of the restriction is the instance's responsibility —
Lean can't structurally enforce "doesn't touch the system."

Motivation: quantum erasure shows that the classical record of a
measurement can be made and unmade unitarily on the apparatus / pointer
states. An agent who cares only about the system should be indifferent
across such erasure/recovery operations.

Structurally this is `IsInvariantUnder` (from `Base`) applied to a
specifically-environmental group action; we expose it as a separate
class because the *conceptual* commitment differs from "preferences are
invariant under the phase group" even when the Lean signature is similar. -/

class AncillaInvariant
    (M : Type u) (E : Type*) [Group E] [MulAction E M] [Preference M] : Prop where
  invariant : ∀ (e : E) (a b : M), (e • a ≼ e • b) ↔ (a ≼ b)

end Qtility
