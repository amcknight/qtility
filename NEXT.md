# Next — threads to pick up

Paused mid-exploration. Build is green (`lake build` works in <1s with the
Mathlib cache reused). Axiom toolkit and two concrete instances compile.

Each thread below has a tag (`V01`, `I01`, …), one or two sentences of context,
the files involved, and a rough complexity estimate. Pick any.

---

## Conversational state (so a fresh session can come up to speed)

- We moved from Agda to Lean 4 + Mathlib v4.30.0. Old Agda files live in
  `agda-archive/` untouched.
- The README is stale — still describes the Agda effort. See `H01` below.
- The axiom toolkit catalog lives in `Qtility/*.lean`; the exploration targets
  catalog lives in `Qtility/Targets.lean`. Reference papers live in `papers/`
  with `papers/README.md` as the index.
- `GLOSSARY.md` (root) is the living concept reference + slug tables — the
  user is learning the underlying math as we go; add entries whenever a new
  concept enters the conversation, and refer to axioms/targets/poisons by
  slug (OBS, XTERM, P-GRID, …) rather than bare numbers.
- `Qtility/Poisons.lean` catalogs construction-level failure modes (P-BOOM
  contradiction, P-MUSH triviality, P-FLOP floppiness, P-TRAP classical
  trapdoor, P-GRID coordinate worship, P-SMUG smuggling, P-VOID vacuity,
  P-EDGE dimension fragility, P-PUMP exploitability) with guards and known
  offenders. New axioms/theorems should be checked against it.
- 2026-06-12 fresh-eyes review found: TH01 needs completeness (or goes
  multi-observable); the qubit is the pathological dimension (Gleason fails
  at n=2 AND 2c is vacuous there); orthogonal states still interfere through
  the observable (⟨a|Ô|c⟩ ≠ 0); proposal to split mixing into cmix/smix with
  a definable "coherence premium." Folded into the threads below.
- The headline result we're aiming at: **Floor + B1 + 2c → observable-valued
  utility** (target #1 in `Targets.lean`). The argument sketch is in a recent
  conversation turn; quickest summary is "B1 makes preferences live on density
  matrices; 2c makes them linear on spectral decompositions; closed-graph gives
  continuity; trace-duality concludes."

---

## V — Axiom verifications (in-code, well-scoped)

### V01 — `HasClosedGraph` for `Lottery`
Show `{(p, q) : p.EU u ≤ q.EU u}` is closed in `Lottery n × Lottery n`.
The topology on `Lottery` is the induced one from `Fin n → ℝ`; you'd lift
continuity of `Finset.sum` and `≤`. **Light** — clean Mathlib continuity proof.
File: `Qtility/Instances/Lottery.lean`.

### V02 — Strengthenings (2b, 2c) for `Lottery`
Verify `MonotoneOwnWeight` and `OrthogonalIndependence` against `EUPref u`.
2c is trivial because classical mixing has no interference (always satisfies
full independence, a fortiori orthogonal). 2b needs a `MixingStructure`
instance — define convex combination of lotteries first.
**Medium** — requires defining the `MixingStructure` instance.
File: `Qtility/Instances/Lottery.lean`.

### V03 — `PosSemidef` for `DensityMatrix`
Mathlib's `Matrix.PosSemidef` on `ℂ`-matrices wants `RCLike`-mediated typeclass
plumbing. Either pull in `Mathlib.LinearAlgebra.Matrix.PosDef` properly or
define a local PSD predicate using `Mathlib.Analysis.InnerProductSpace.Spectrum`
for the spectral decomposition. **Medium-heavy** — proof obligation isn't hard
but typeclass setup is fiddly.
File: `Qtility/Instances/Qubit.lean`.

### V04 — B1 and 2c for `Qubit`
`RespectsOperationalEquivalence` is essentially free — the preference is
*defined* via `ρ.M`, so it factors through density-matrix equality by
construction. Stating it cleanly requires an `OperationalEquivalence` instance
mapping `opEquiv ρ σ := ρ.M = σ.M`. 2c needs a `MixingStructure` (convex combo
of density matrices) and an `Orthogonality` predicate (`Tr(ρ_a · ρ_c) = 0`).
**Medium** for B1, **medium-heavy** for 2c.
File: `Qtility/Instances/Qubit.lean`.

### V05 — `IsInvariantUnder Unit` for `Lottery`
The trivial classical phase group. Sort out `Unit`'s `Group` instance imports
(I bounced off this once — the right import isn't `Mathlib.Algebra.Group.Defs`).
**Light** once the right import is found. File: `Qtility/Instances/Lottery.lean`.

### V06 — `IsInvariantUnder Circle` for `DensityMatrix`
Global phase on state vectors `ψ ↦ e^{iθ}ψ` lifts to `ρ ↦ ρ` on density
matrices — trivially invariant. Needs `Mathlib.Analysis.SpecialFunctions.Complex.Circle`
or similar. **Light**. File: `Qtility/Instances/Qubit.lean`.

---

## I — New instances

### I01 — Rebit instance (`ℝ²` real amplitudes)
Halfway between classical lottery and qubit: real-amplitude superpositions on
2 states with `α² + β² = 1`. Gets interference (negative amplitudes cancel)
but no phase. Useful for comparing axiom satisfaction across the
classical → rebit → qubit spectrum. **Medium**.
New file: `Qtility/Instances/Rebit.lean`.

### I02 — Qudit instance (promote the qutrit)
Generalize `Qubit` to `DensityMatrix n` for arbitrary `n`. Most of the
machinery is already general — `DensityMatrix` already takes `n`. May be
free once V03/V04 settle. **Light** mostly.
Upgraded importance after the 2026-06-12 review: the **qutrit (n=3) should
be the flagship**, not the qubit — Gleason fails at n=2 and 2c/SAFEIND is
vacuous there (see P-EDGE, P-VOID in `Qtility/Poisons.lean`).
Same file or new: `Qtility/Instances/Qudit.lean`.

### I03 — Coherent-state instance (continuous, exotic)
Field-theoretic coherent states (e.g. `|α⟩` for `α ∈ ℂ`). These are
infinite-dimensional and form an overcomplete set; not a finite Hilbert
space. Would test whether axioms still make sense in the infinite-dim
limit. **Heavy / research-grade**. Optional.

---

## TH — Theorem threads

### TH01 (REP) — State the representation theorem
Write `Qtility/Theorems/ObservableRepresentation.lean` with the theorem
statement (no proof yet):

> Given any `Preference (DensityMatrix n)` satisfying `IsReflexive`,
> `IsTransitive`, **totality**, `HasClosedGraph`, `RespectsOperationalEquivalence`,
> and `OrthogonalIndependence`, **with `n ≥ 3`**, there exists a Hermitian `Ô`
> and constants `a > 0`, `b ∈ ℝ` such that the preference agrees with
> `ObservablePref (a·Ô + b·I)`.

Two caveats from the 2026-06-12 review (see `Qtility/Poisons.lean`):
* **Completeness is required** (P-FLOP): the identity preference satisfies
  all the other hypotheses and is represented by no observable. Fork: add an
  `IsTotal` axiom, or aim for a multi-observable (quantum Aumann)
  representation — could become target #7.
* **`n ≥ 3` is required** (P-EDGE): Gleason fails at n=2 (odd functions on
  the Bloch sphere give non-linear counterexamples, e.g. u = r_z³/|r|²),
  and 2c/SAFEIND is vacuous at n=2 anyway (P-VOID). Either make the qutrit
  the flagship or take the POVM route: R1/ANCILLA + Naimark dilation ≈
  Busch's POVM-Gleason, which holds at every n.

Stating this precisely is most of the design work. **Medium** for the statement
alone. **Heavy** for the proof (likely a Gleason-style argument + trace duality).

### TH02 — Forward direction for Qubit
The instance-level statement: for any Hermitian `Ô`, `ObservablePref Ô`
satisfies Floor + B1 + 2c. Reduces to V04 + V06.

### TH03 — Affine uniqueness
Any two observables that induce the same preference relation differ by a
positive affine transformation: `Ô' = a·Ô + b·I` with `a > 0`. Classical
vNM affine uniqueness lifted to operators. **Medium**.

### TH04 — Classical recovery
Floor + B1 + 2c + `PostDecoherenceClassical` (E2) collapses to classical
EU on the diagonal. A "trapdoor confirmation" theorem — shows our toolkit
correctly identifies the classical limit. **Light** once TH01 is settled.

### TH05 — Positive observable theorem (revised 2026-06-12)
Originally: Floor + B1 + 2c + sign-blind NMP → `Ô` PSD. The sign-blind NMP
turned out to smuggle in the conclusion — under the linear trace extension
it forbids any below-null ("hell") branch, so PSD-ness was an artifact.
NMP is now sign-aware (shrinking measure moves you toward `null`), and
under the linear extension it is satisfied by *every* Hermitian `Ô` —
no positivity falls out. Revised statement:

> (a) Floor + B1 + 2c + `NullIsWorst` → `Ô ⪰ 0` (modulo affine). The
> floor is now an explicit, honest axiom rather than a pump side effect.
> (b) Cone-extension classification: on the subnormalized cone, sign-blind
> NMP ⇔ linear extension + PSD; sign-aware NMP ⇔ linear extension, any
> Hermitian `Ô`; `MeasureIndifference` ⇔ ray/renormalized extension, any
> `Ô`. The representation theorem (TH01) lives on the normalized slice
> and is untouched by the choice.

**Light** for (a) once TH01 is settled; **medium** for (b).

---

## A — Axiom-toolkit extensions

### A01 — Concretize `CompoundReduction` (2a)
Currently a `True` placeholder. Needs an algebra on the `Param` type so we
can express `compose p q` and state the reduction equation. Probably best
done per-instance (one statement per `MixingStructure`). Decide whether 2a
remains schematic or gets an instance-specific concrete form.
File: `Qtility/Mixing.lean`. **Medium** for thinking, **light** for code.

### A02 — Codimension-1 indifference (C4)
Currently deferred (just a comment). Needs manifold/smooth structure on `M`.
Once we commit to a state space (likely projective Hilbert space `ℂP^n` as a
Kähler manifold), C4 becomes statable. **Medium** — pull in
`Mathlib.Geometry.Manifold.SmoothManifoldWithCorners` etc.
File: `Qtility/Continuity.lean`.

### A03 — Interference-primitive axiom (for target #5)
We don't yet have an axiom that *directly* talks about interference cross-terms.
For target #5 (interference-as-information) we'd want something like:
"preferences are monotone in `Re(α·β̄·⟨ψ₁|Ô|ψ₂⟩)` for some Ô," but framed
abstractly. Worth designing carefully — it's a genuinely new primitive with
no classical analog. **Heavy** — research-grade design.

### A04 — Bell-correlation axiom (B2?)
Beyond plain B1, there might be sharper axioms inspired by Bell experiments
specifically — e.g., preferences on entangled states should reflect the
no-signaling principle. Not yet drafted. Worth a brainstorm session.
File: `Qtility/PhysicalAxioms.lean`.

### A05 — Decoherence-cost axiom
Drawing on Landauer's principle: preferences should respect the
thermodynamic cost of erasure. Not yet drafted. Possibly subsumes the
NMP axiom in a strict form. Worth designing.
File: `Qtility/PhysicalAxioms.lean`.

### A06 — Split mixing into cmix/smix; define the coherence premium
`MixingStructure` currently conflates two different operations: classical
convex mixture of density matrices (cmix — no interference) and
superposition with complex weights (smix — interference; only total on the
subnormalized cone). Make both first-class. Then the **coherence premium**
`u(smix p a b) − u(cmix |p|² a b)` becomes definable: targets BONUS and
XTERM are statements about it, and E1/BORNTRAP is exactly "premium ≡ 0."
Note the motivating subtlety: orthogonal states still interfere *through
the observable* (`⟨a|Ô|c⟩ ≠ 0` despite `⟨a|c⟩ = 0`), so SAFEIND is only
safe for cmix, not smix. **Medium** design, **medium** code.

Deeper design problem (2026-06-12, from the "rescuing summing" discussion):
smix is ill-defined on *physical* states — superposition needs
representatives (gauge); the physical parameterization is weight +
relative phase (segment × circle; sphere surface for a qubit). Options:
(a) define smix on vectors and demand all smix-axioms be phase-covariant;
(b) put the relative phase explicitly into `Param`;
(c) treat mixing as a *process* primitive (beamsplitter channel) and fold
into the operations layer (A07).
This choice shapes every mixing-family axiom — decide before formalizing.
File: `Qtility/Mixing.lean`.

### A07 — NoPump schema (operations layer)
Every Dutch-book motivation (NMP, COHUP's Mach–Zehnder) quantifies over
adversary *operations* that the formalism doesn't contain — we only have
states. Add an operations monoid acting on `M` with a cost function, and
one NoPump meta-axiom: no cycle returning to the start with every step
weakly preferred and negative total cost. NMP, COHUP, and the classical
money pump become instances; P-PUMP becomes statable. Answers D05
structurally. **Heavy** design, research-grade — but the unifying payoff
is large.
New file: `Qtility/Operations.lean`.

---

## D — Discussion threads (talk before coding)

The user explicitly said "lots more I want to talk about." These are the
on-deck topics:

### D01 — More physical experiments to inspire axioms
General brainstorming continues. Past suggestions: Bell, Everett, Mach–Zehnder,
quantum eraser, Landauer. Likely candidates: contextuality experiments,
weak-measurement protocols, post-selection.

### D02 — Deutsch–Wallace branch aggregation literature
The full E1 (Born equivalence) axiom recovers classical vNM via the
Deutsch–Wallace research program. Worth surveying that literature so we
know what's been done in this neighborhood. Cite: Deutsch 1999, Wallace
*The Emergent Multiverse* (2012). Papers not in `papers/` yet; could add.

### D03 — Resource theory of coherence
Modern quantum information has a formal "resource theory of coherence"
(Baumgratz, Cramer, Plenio 2014 and follow-ups). The C1 monotone-in-coherence
axiom connects directly. Papers could be added to `papers/` for grounding.

### D04 — Quantum erasure + Landauer connections
Discussed but didn't formalize. Possible axiom: "erasure has a thermodynamic
cost reflected in preferences." Connects to A05.

### D05 — What does "infinite value" / "money pump" mean structurally?
The user proposed the measure-pump (now sign-aware NMP; the sign-blind
form was retired 2026-06-12 — it secretly forbade below-null branches).
Open question from that discussion: is `MeasureIndifference` (the
"cancel it out by renormalizing" stance) Dutch-bookable when conditioning
costs resources? Connects to A05/Landauer. There may be other generalized
Dutch-book arguments worth exploring: interferometric, post-selection,
entanglement-distillation.

### D07 — Born-but-not-vNM: risk attitudes over branch measure
User question (2026-06-12): "back to Born is fine if it doesn't lead back
to vNM — does it always?" Answer: no — the trapdoor has two floors (see
GLOSSARY "The two trapdoors"). Born-collapse lands in lottery-land but
leaves independence undecided; non-EU preferences over branch weights
(rank-dependent, variance-averse, maximin) remain coherent. This is the
fault line of the Deutsch–Wallace debate (D02): their rationality axioms
force both floors, critics attack the second. Candidate future target:
RISK — "Born weights + non-EU risk attitude" representation.

### D06 — Categorical / non-representation routes (target #6)
If we can't get a single-function representation, what *shape* of
representation does the quantum case demand? Sheaves over orthonormal bases?
Functors? Worth thinking about before declaring "no representation."

---

## H — Housekeeping

### H01 — README rewrite — DONE 2026-06-12
Rewritten: Lean toolkit framing, orientation table (GLOSSARY/NEXT/Targets/
Poisons/axiom files/instances), status, build instructions.

### H02 — Optional CI
`lake new` scaffolded GitHub Actions in the temp dir that we didn't keep.
If the project gets serious, copy in `.github/workflows/lean_action_ci.yml`
to verify each commit builds.

### H03 — Possibly switch to `Mathlib.Tactic` broad import for instance files
The instances are exploratory; tighter imports keep failing on Mathlib's
moving file structure. Just importing `Mathlib.Tactic` would absorb the
toolchain churn. Trade-off: slower build per file (~5s extra) for fewer
breakage points.

---

## Layout reference

```
qtility/
├── Qtility.lean             # entry, imports all
├── Qtility/
│   ├── Base.lean            # floor axioms
│   ├── Mixing.lean          # 2a, 2b, 2c + MixingStructure / Orthogonality
│   ├── Symmetry.lean        # 4a, 4c
│   ├── Continuity.lean      # C3; C4 deferred
│   ├── PhysicalAxioms.lean  # B1, E2, C1, R1, sign-aware NMP, MeasureIndifference, NullIsWorst, OperationalEquivalence, HasMeasure
│   ├── Targets.lean         # named exploration targets catalog (slugs: OBS, BONUS, CTX, LEX, XTERM, NOREP)
│   ├── Poisons.lean         # construction-level failure modes (P-BOOM … P-PUMP)
│   └── Instances/
│       ├── Lottery.lean     # classical EU lotteries
│       └── Qubit.lean       # density matrices + observable preference
├── agda-archive/            # original Agda work, untouched
├── papers/                  # reference PDFs + index
├── GLOSSARY.md              # living concept reference + slug tables (add as we go)
├── README.md                # rewritten 2026-06-12 (H01 done)
├── lakefile.toml            # Mathlib v4.30.0 dependency
├── lean-toolchain           # leanprover/lean4:v4.30.0
└── NEXT.md                  # this file
```
