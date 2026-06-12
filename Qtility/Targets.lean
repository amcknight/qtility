/-
# `Qtility.Targets` — exploration target catalog

A structured catalog of "fun results" we might aim for in the toolkit.
Each target is a `Target` value with:
  * a short name and one-line summary
  * an axiom *recipe* — combinations expected to land it
  * axioms to *avoid* — additions that would trivialize or sink it
  * a status field
plus a free-form Lean docstring with the detailed motivation.

This file is meant to be browsed, grepped, and added to as ideas surface.
Reading order: structure definition, then each target.

The current targets are #1 `observableUtility`, #2 `coherenceAxis`,
#3 `contextualUtility`, #4 `lexicographicUtility`, #5 `interferenceAsInformation`,
#6 `noRepresentation`. Add more freely.
-/

namespace Qtility.Target

/-! ## The Target structure -/

/-- A named exploration target. Mostly documentation, with structured
metadata for quick scanning. -/
structure Target where
  /-- Conversation slug (e.g. "OBS", "XTERM") — see `GLOSSARY.md` tables. -/
  slug : String
  /-- Short identifier (slug-ish, human-readable). -/
  name : String
  /-- One-line summary of the intended result. -/
  oneLine : String
  /-- Short labels of axioms expected to help land this target. -/
  recipe : List String
  /-- Short labels of axioms whose adoption would sink or trivialize this target. -/
  avoid : List String
  /-- Free-form status: "open", "explored", "sunk by X", "achieved", etc. -/
  status : String
  deriving Inhabited, Repr

/-! ## #1 — Observable-valued utility -/

/-- # Observable-valued utility

The agent's preferences are encoded by a self-adjoint operator `Û` on the
Hilbert space, with `ψ ≼ ψ' ⟺ ⟨ψ|Û|ψ⟩ ≤ ⟨ψ'|Û|ψ'⟩`. This is the quantum
analog of classical scalar utility lifted via expectations.

**Why interesting:** quantum observables would not be *imposed* by the
formalism — they'd fall out of decision theory the same way scalar
utility functions do classically. That would be a philosophical claim
about why physics looks the way it does.

**Status:** primary candidate target. Cleanest path. Probably tractable
with the recipe below. -/
def observableUtility : Target := {
  slug := "OBS"
  name := "Observable-valued utility"
  oneLine := "Preferences represented by a self-adjoint operator Û (quadratic in amplitudes)"
  recipe := [
    "RespectsOperationalEquivalence (B1)",
    "OrthogonalIndependence (2c)",
    "CompoundReduction (2a)",
    "AncillaInvariant (R1)" ]
  avoid := [
    "Full Born equivalence (E1)",
    "Full unitary invariance (4d)" ]
  status := "open — primary candidate"
}

/-! ## #2 — Coherence as a separate utility axis -/

/-- # Coherence as a separate utility axis

Preferences decompose into a "diagonal utility" (the Born-distribution
piece, recovering classical EU) plus a *separate* "coherence bonus" that
depends on the off-diagonal density matrix terms.

**Why interesting:** strictly richer than classical. The agent values
quantum coherence as such, independent of probabilistic outcomes. The
classical limit recovers exactly as the coherence weight goes to zero.

**Status:** open. Requires keeping the off-diagonal structure visible
through the axioms — adopting `PermutationInvariant` (4a) **and**
`PerOutcomePhaseInvariant` (4c) together would erase exactly this. -/
def coherenceAxis : Target := {
  slug := "BONUS"
  name := "Coherence axis"
  oneLine := "Utility decomposes into Born-EU + coherence-bonus"
  recipe := [
    "RespectsOperationalEquivalence (B1)",
    "OrthogonalIndependence (2c)",
    "MonotoneOwnWeight (2b)",
    "MonotoneInCoherence (C1)",
    "AncillaInvariant (R1)" ]
  avoid := [
    "PermutationInvariant + PerOutcomePhaseInvariant together (4a+4c)",
    "PostDecoherenceClassical at full E1 strength" ]
  status := "open"
}

/-! ## #3 — Contextual utility -/

/-- # Contextual utility

No single global utility function exists. Instead, for each "measurement
context" (each orthonormal basis), there's a context-relative utility.
Preferences between states not sharing a context are governed by
something other than utility comparison.

**Why interesting:** parallels Kochen–Specker contextuality. Would
constitute a decision-theoretic version of the impossibility of
non-contextual hidden variables.

**Status:** speculative. Requires giving up `RespectsOperationalEquivalence`
or restricting it severely, since context-dependence violates basis-
independence. -/
def contextualUtility : Target := {
  slug := "CTX"
  name := "Contextual utility"
  oneLine := "Per-basis utility, no single global representation"
  recipe := [
    "OrthogonalIndependence (2c) restricted to within-basis cases",
    "PermutationInvariant (4a) restricted to a fixed basis" ]
  avoid := [
    "RespectsOperationalEquivalence (B1)",
    "AncillaInvariant in its strongest form",
    "CompoundReduction (2a) across contexts" ]
  status := "open — speculative"
}

/-! ## #4 — Lexicographic (vector-valued) utility -/

/-- # Lexicographic / vector-valued utility

Utilities are *vectors*, ordered lexicographically. Generalizes Hausner's
classical drop-Archimedean construction (see
`papers/1952-hausner-multidimensional-utilities-rand.pdf`).

In the quantum setting, interference can drive preferences in
incommensurable directions, so the utility splits into a tuple of
independent components.

**Why interesting:** ties to a known classical result with a natural
quantum lift. Hausner's framework is well-understood; a quantum analog
would be a clean extension. -/
def lexicographicUtility : Target := {
  slug := "LEX"
  name := "Lexicographic utility"
  oneLine := "Vector-valued utility ordered lexicographically (Hausner-style)"
  recipe := [
    "MonotoneOwnWeight (2b)",
    "OrthogonalIndependence (2c)" ]
  avoid := [
    "HasConnectedIndifference (C3)",
    "C4 codimension-1 indifference" ]
  status := "open"
}

/-! ## #5 — Interference-as-information -/

/-- # Interference as information

The utility of a superposition `αψ₁ + βψ₂` contains a term that depends
explicitly on the interference cross-term `Re(α·β̄ · ⟨ψ₁|Ô|ψ₂⟩)` for some
operator `Ô`. Interference acts as a *separate channel* of utility,
distinct from the marginal valuations of `ψ₁` and `ψ₂`.

**Why interesting:** would be the cleanest "genuinely new primitive" —
something with no classical analog at all. Most speculative target;
likely needs a new axiom we haven't yet named (an "interference
primitive").

**Status:** open. Probably the most exciting if it works. -/
def interferenceAsInformation : Target := {
  slug := "XTERM"
  name := "Interference-as-information"
  oneLine := "Utility has an explicit interference cross-term — new primitive"
  recipe := [
    "RespectsOperationalEquivalence (B1)",
    "AncillaInvariant (R1)",
    "MonotoneInCoherence (C1)",
    "+ new axiom — interference primitive (TBD)" ]
  avoid := [
    "Full Born equivalence (E1)",
    "PermutationInvariant + PerOutcomePhaseInvariant together" ]
  status := "open — most speculative, most exciting"
}

/-! ## #6 — No representation at all -/

/-- # No single-function representation

Negative result: under our intended axiom combinations, no single
function `f : States → ℝ` (or vector-valued analog) suffices to
represent the preference. The structure has to be characterized as a
*category* or *space* of preferences, not as a sublevel structure.

**Why interesting:** a negative theorem is still a theorem. It would
say the classical "utility function" framework was always parochial
and the quantum case demands a different *shape* of representation. -/
def noRepresentation : Target := {
  slug := "NOREP"
  name := "No representation"
  oneLine := "Negative: no single-function representation; characterize the space instead"
  recipe := [
    "Strong axioms but pairwise incompatible (e.g., B1 + #3-style contextuality)" ]
  avoid := [
    "Any combination that lands #1-#5" ]
  status := "open — fallback / characterization result"
}

/-! ## Catalog -/

/-- All currently-tracked targets, for `#eval allTargets` in the editor. -/
def allTargets : List Target := [
  observableUtility,
  coherenceAxis,
  contextualUtility,
  lexicographicUtility,
  interferenceAsInformation,
  noRepresentation ]

end Qtility.Target
