/-
# `Qtility.Poisons` — failure modes the whole construction must avoid

Where `Targets.lean` catalogs what we *want*, this file catalogs what we
must *not* end up with. Each poison is a way an axiom system can go wrong
that is invisible from inside any single proof — you only see it by asking
meta-questions ("does this bundle have a model?", "is the model boring?").

Each `Poison` has a slug (use these in conversation), a detection guard,
and the known offenders in this repo — current or retired. The guards are
informal for now; several could become literal Lean obligations per axiom
bundle (e.g. P-BOOM and P-MUSH guards are satisfiability witnesses).

See `GLOSSARY.md` for the concept background and the slug tables.
-/

namespace Qtility.Poison

/-- A named failure mode of the construction, with a detection guard. -/
structure Poison where
  /-- Short slug, used in conversation (e.g. "P-TRAP"). -/
  slug : String
  /-- Human-readable name. -/
  name : String
  /-- One-line description of the failure. -/
  oneLine : String
  /-- How to detect it / what proof obligation guards against it. -/
  guard : String
  /-- Known offenders in this repo, current or retired. -/
  offenders : List String
  deriving Inhabited, Repr

/-- # P-BOOM — contradiction
The axiom bundle is unsatisfiable: no preference on any state space meets
all of it. Worthless in the most direct way — every theorem about it is
vacuously true. -/
def contradiction : Poison := {
  slug := "P-BOOM"
  name := "Contradiction"
  oneLine := "the axiom bundle has no model at all"
  guard := "every adopted bundle ships with at least one verified instance \
            (this is what Instances/ is for — instances are consistency proofs)"
  offenders := ["none known"]
}

/-- # P-MUSH — triviality
Satisfiable, but only by degenerate preferences: total indifference, or
the identity preference. The theory "works" and says nothing. -/
def triviality : Poison := {
  slug := "P-MUSH"
  name := "Triviality"
  oneLine := "only degenerate preferences (total indifference, identity) survive"
  guard := "exhibit a model with at least two strictly-ranked states; \
            a satisfiability witness that is not the trivial preference"
  offenders := [
    "4a+4c jointly: collapse to symmetric functions of the Born distribution",
    "4a alone already forces a near-uniform utility observable — stronger than advertised" ]
}

/-- # P-FLOP — floppiness
A representation exists but isn't pinned: many inequivalent representers,
freedom beyond the stated affine slack. The classical antidote is a
uniqueness clause (vNM: unique up to positive affine). -/
def floppiness : Poison := {
  slug := "P-FLOP"
  name := "Floppiness"
  oneLine := "the representation exists but is not pinned up to stated freedom"
  guard := "every representation theorem must carry its uniqueness clause (TH03/AFFU-style)"
  offenders := [
    "TH01 without completeness: the identity preference satisfies all hypotheses \
     and is represented by no observable",
    "n = 2 frame functions: u = r_z³/|r|² on the Bloch ball is linear on every \
     spectral decomposition yet is no observable — Gleason fails for qubits" ]
}

/-- # P-TRAP — classical trapdoor
The bundle quietly forces preferences to factor through Born
distributions: we rebuilt classical vNM with extra steps and the quantum
structure is invisible. Note the nuance: classical recovery *on demand*
(TH04/CLREC, adding E2 deliberately) is a feature; falling through the
trapdoor uninvited is the poison.

The trapdoor has **two floors** (see GLOSSARY "The two trapdoors"):
(1) *Born-collapse* — preferences factor through one privileged basis's
Born lottery; (2) *vNM-collapse* — preferences are additionally EU-linear
in those weights. Born-without-vNM is a legitimate exploratory position
(risk attitudes over branch measure, thread D07); guard each floor
separately. -/
def classicalTrapdoor : Poison := {
  slug := "P-TRAP"
  name := "Classical trapdoor"
  oneLine := "axioms secretly force preferences to be functions of Born statistics"
  guard := "guard each floor separately: (1) Born-collapse — exhibit two states \
            with identical Born statistics in the relevant bases that can still \
            be ranked strictly; (2) vNM-collapse — check whether independence-\
            strength axioms force EU-linearity in the Born weights"
  offenders := [
    "E1/BORNTRAP — by design; that is why it is not adopted",
    "4a+4c jointly",
    "sign-blind NMP pushed toward classical linearity in measure (retired 2026-06-12)" ]
}

/-- # P-GRID — coordinate worship
An axiom or representation privileges a basis or labeling without physical
warrant — preferences about coordinates rather than physical possibilities.
The one legitimate exception is a decoherence pointer basis, and any axiom
using it must name it as such. -/
def coordinateWorship : Poison := {
  slug := "P-GRID"
  name := "Coordinate worship"
  oneLine := "privileging a basis/labeling without physical justification"
  guard := "state axioms covariantly (invariant under unitary change of description) \
            unless physics supplies the basis; pointer-basis exceptions must be explicit"
  offenders := [
    "4a/SHUFFLE and 4c/DIAL each act in a fixed basis — adopt only with the basis justified",
    "E2/POSTCLASS's isClassical predicate — legitimate only if tied to a pointer basis",
    "any future per-basis utility (target CTX) must carry its context explicitly" ]
}

/-- # P-SMUG — smuggling
The headline conclusion is hiding inside an axiom; the theorem is a
restatement, not a derivation. Detected by asking what each axiom forces
*alone*. -/
def smuggling : Poison := {
  slug := "P-SMUG"
  name := "Smuggling"
  oneLine := "the conclusion was packed into an axiom; the theorem is a restatement"
  guard := "for each axiom, document its solo footprint — what it forces by itself \
            on the flagship instance"
  offenders := [
    "retired sign-blind NMP: forced PSD single-handedly, which was then 'derived' (TH05)",
    "B1/OPEQ carries the full operational structure of QM — acceptable, but must be \
     acknowledged as the physics input, not a neutral rationality axiom" ]
}

/-- # P-VOID — vacuity
An axiom whose hypothesis never (or barely) fires on the instance:
satisfied for free, constraining nothing, while appearing on the
hypothesis list and taking credit. -/
def vacuity : Poison := {
  slug := "P-VOID"
  name := "Vacuity"
  oneLine := "an axiom whose hypothesis never fires on the instance — satisfied for free"
  guard := "for each axiom × instance pair, exhibit a nontrivial witness of the \
            hypothesis actually firing"
  offenders := [
    "2c/SAFEIND on qubits: 'a, b both orthogonal to c' forces a = b when n = 2 — \
     the workhorse axiom is empty on the flagship instance",
    "NMP on trace-1 states: measure is constantly 1, hypothesis never fires \
     (needs the subnormalized cone)",
    "2a/FLATTEN is literally `True` right now (thread A01)" ]
}

/-- # P-EDGE — edge-dimension fragility
A result that holds only in a special dimension or corner of the state
space — especially dangerous when the flagship instance lives exactly
there. -/
def edgeFragility : Poison := {
  slug := "P-EDGE"
  name := "Edge-dimension fragility"
  oneLine := "true only at special dimensions/corners — and the flagship may live there"
  guard := "check every claim at n = 2, n = 3, large n, pure and mixed states, \
            before celebrating"
  offenders := [
    "Gleason's theorem fails at n = 2: the qubit flagship is the one pathological \
     dimension; promote the qutrit or take the POVM/ancilla (Busch) route" ]
}

/-- # P-PUMP — exploitability
The bundle leaves an open Dutch book: an adversary with allowed operations
can extract unbounded value from an agent obeying the axioms. Currently
not even *statable* — the formalism has states but no operations layer.
See the NoPump schema thread (A07) and D05. -/
def exploitability : Poison := {
  slug := "P-PUMP"
  name := "Exploitability"
  oneLine := "an open Dutch book survives — adversary extracts unbounded value"
  guard := "needs an operations layer (operations monoid + cost) to state; \
            until then, informal pump checks per axiom"
  offenders := [
    "MeasureIndifference/RENORM if renormalization is not free — open question (D05)" ]
}

/-- All currently-tracked poisons, for `#eval allPoisons` in the editor. -/
def allPoisons : List Poison := [
  contradiction,
  triviality,
  floppiness,
  classicalTrapdoor,
  coordinateWorship,
  smuggling,
  vacuity,
  edgeFragility,
  exploitability ]

end Qtility.Poison
