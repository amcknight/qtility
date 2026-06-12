/-
# `Qtility.Base` — the floor

Axioms we adopt before any quantum/classical commitments. These are
intentionally *floppy*: any continuous preference relation on a state space
can satisfy them. The interesting commitments live in `Qtility.Strengthenings`.

Adopted here:
  * Reflexivity                    `a ≼ a`
  * Transitivity                   chains compose
  * Closed-graph regularity (S1)   `≼` is closed in `M × M`
  * Closed indifference (C2)       each indifference class is closed in `M`
  * Phase / projective (S2)        preferences invariant under a designated
                                   group action (e.g. global U(1) for qubits)

Notation introduced (all scoped to `Qtility`):
  `a ≼ b`   weak preference
  `a ≈ b`   indifference
  `a ≺ b`   strict preference
-/

import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Constructions
import Mathlib.Algebra.Group.Action.Defs

namespace Qtility

universe u

/-! ## The preference relation -/

/-- A binary preference relation on states `M`. -/
class Preference (M : Type u) where
  /-- `pref a b` reads "`a` is at most as preferred as `b`" (notation: `a ≼ b`). -/
  pref : M → M → Prop

@[inherit_doc Preference.pref]
scoped notation:50 a " ≼ " b => Preference.pref a b

/-- Indifference: weak preference both ways. -/
def Indifferent {M : Type u} [Preference M] (a b : M) : Prop :=
  (a ≼ b) ∧ (b ≼ a)

@[inherit_doc Indifferent]
scoped notation:50 a " ≈ " b => Indifferent a b

/-- Strict preference: `a ≼ b` and not `b ≼ a`. -/
def StrictPref {M : Type u} [Preference M] (a b : M) : Prop :=
  (a ≼ b) ∧ ¬ (b ≼ a)

@[inherit_doc StrictPref]
scoped notation:50 a " ≺ " b => StrictPref a b

/-! ## Floor axiom: reflexivity -/

/-- Every state is at least as preferred as itself. -/
class IsReflexive (M : Type u) [Preference M] : Prop where
  refl : ∀ a : M, a ≼ a

/-! ## Floor axiom: transitivity -/

/-- Preference chains compose. -/
class IsTransitive (M : Type u) [Preference M] : Prop where
  trans : ∀ {a b c : M}, (a ≼ b) → (b ≼ c) → (a ≼ c)

/-! ## Floor axiom: closed-graph regularity (S1)

The preference relation is a closed subset of `M × M` under the product
topology. Equivalently: if `aₙ → a`, `bₙ → b`, and `aₙ ≼ bₙ` for all `n`,
then `a ≼ b`. "Limits of preferences are preferences."

This is the relational version of "preferences are continuous." It implies
`HasClosedIndifference` (below) but we list both so the strengthenings can
require either independently. -/

class HasClosedGraph (M : Type u) [TopologicalSpace M] [Preference M] : Prop where
  closed : IsClosed { p : M × M | p.1 ≼ p.2 }

/-! ## Floor axiom: closed indifference (C2 — partition continuity at base strength)

The indifference class of each state `b` is a closed subset of `M`. This is
the topological reformulation of "the indifference boundary between `≻ b`
and `≺ b` is well-defined."

Implied by `HasClosedGraph`; included separately for ergonomics. -/

class HasClosedIndifference (M : Type u) [TopologicalSpace M] [Preference M] : Prop where
  closed : ∀ b : M, IsClosed { a : M | a ≈ b }

/-! ## Floor axiom: phase / projective well-definition (S2)

Preferences are invariant under a designated "phase" group action `G ⟶ M`.

| Setting             | `G`                  | Action                          |
| ------------------- | -------------------- | ------------------------------- |
| Classical lottery   | `Unit`               | trivial                         |
| Rebit               | `ZMod 2`             | sign flip on the state vector   |
| Qubit               | `Circle` (U(1))      | scalar mult by `e^{iθ}`         |

This *is* phase invariance #3 from the axiom discussion — recast as the
formal statement that preferences live on the orbit space rather than on
state vectors. -/

class IsInvariantUnder
    (G : Type*) [Group G] (M : Type u) [Preference M] [MulAction G M] : Prop where
  invariant : ∀ (g : G) (a b : M), (g • a ≼ g • b) ↔ (a ≼ b)

end Qtility
