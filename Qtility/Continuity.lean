/-
# `Qtility.Continuity` — stronger continuity axioms

The floor already commits to closed-graph regularity (S1) and closed
indifference (C2). This file holds the stronger options up the ladder.

Contents:
  * `HasConnectedIndifference` (C3)
  * C4 (codimension-1 indifference) — deferred, see end of file
-/

import Qtility.Base
import Mathlib.Topology.Connected.PathConnected

namespace Qtility

universe u

/-! ## C3 — Connected indifference classes

Each indifference class is path-connected: you can walk between any two
indifferent states staying inside the indifference class.

Strictly stronger than `HasClosedIndifference` (C2). Rules out the case
where the indifference class breaks into disconnected components, which
would mean the preference can "jump" across boundaries without revealing
itself in between. -/

class HasConnectedIndifference (M : Type u) [TopologicalSpace M] [Preference M] : Prop where
  connected : ∀ b : M, IsPathConnected { a : M | a ≈ b }

/-! ## C4 — Codimension-1 indifference (deferred)

Each indifference class is locally a hypersurface (codimension 1 in `M`).
Rules out fractal/degenerate level sets; amounts to saying the preference
function is smooth enough to admit a well-defined gradient direction.

Stating this requires a manifold/smooth structure on `M`, which in turn
requires committing to a specific state space (e.g. projective Hilbert
space `ℂP^n` as a Kähler manifold). We leave this as a signature only
for now.
-/

-- class HasCodimensionOneIndifference (M : Type u) [Preference M] [SmoothManifold M] : Prop where
--   codim_one : ...   -- TODO once state space is committed

end Qtility
