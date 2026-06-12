# Glossary

Living reference for the concepts behind qtility. Entries build on earlier
ones, so reading top-to-bottom is a mini-course, but it's designed for
jumping into. Each entry ends with a *Here:* line saying why it matters in
this project. Slug tables (axioms, targets, theorems, poisons) are at the
bottom — those are the short names we use in conversation.

Add entries whenever a new concept shows up. Entries marked ★ are the
load-bearing ones.

---

## Part I — Classical decision theory

### Preference relation (≼)
A binary relation on a space of options: `a ≼ b` reads "b is at least as
good as a." Everything else is derived: *indifference* (`a ≈ b`, both
directions) and *strict preference* (`a ≺ b`, one direction only). No
numbers anywhere yet — preferences are the primitive, utility is what you
hope to *earn* from them via a theorem.
*Here:* the `Preference` class in `Base.lean`; the whole project asks which
axioms on ≼ force which numerical (or operator-valued) representations.

### Representation theorem
A theorem of the form: "any preference satisfying axioms X, Y, Z can be
written as `a ≼ b ⟺ f(a) ≤ f(b)` for some function f of a specific shape."
The axioms are the philosophy; the representation is the payoff. The
classical prize is the vNM theorem (below).
*Here:* TH01/REP is our hoped-for quantum analog, with f(ρ) = Tr(ρÛ).

### Completeness (totality)
The demand that *any* two options are comparable: `a ≼ b` or `b ≼ a`,
always. Sounds innocent, is actually a heavyweight: it forbids "I genuinely
can't rank these." Without it, no single real-valued function can represent
the preference (a function always ranks everything). Aumann (1962, in
`papers/`) started the study of dropping it — you then get *sets* of utility
functions, with `a ≼ b` meaning *all* of them agree.
*Here:* our floor deliberately omits it. That's a fork we must choose at
TH01: add totality, or aim for a multi-*observable* representation
(a quantum Aumann). The identity preference ("only a ≼ a") satisfies every
current axiom and represents nothing — see poison P-FLOP.

### Lottery, expected utility (EU)
A lottery is a probability distribution over n outcomes — a vector
(p₁,…,pₙ), each pᵢ ≥ 0, summing to 1. Given a utility uᵢ per outcome,
the *expected utility* of the lottery is Σ pᵢuᵢ. Comparing lotteries by EU
is the classical model of rational choice under risk.
*Here:* `Lottery.lean`, the sanity-check instance. The founding observation
of this project: a lottery's data (nonneg reals summing to 1) looks
suspiciously like a quantum state's data (complex amplitudes,
norms-squared summing to 1).

### vNM theorem, affine uniqueness
Von Neumann–Morgenstern (1947): a preference on lotteries satisfies
completeness + transitivity + continuity + independence **iff** it's
expected utility for some outcome-utility u — and u is unique *up to
positive affine transformation* (au + b, a > 0; the Celsius/Fahrenheit
freedom). That uniqueness clause is what makes the representation
*pinned* rather than floppy.
*Here:* the template. TH01 is "vNM where the simplex becomes the density
matrix body"; TH03/AFFU is the uniqueness clause, Û' = aÛ + bI.

### The thermometer construction (calibration)
How the vNM proof actually *uses* mixing. Fix a best outcome and a worst
outcome. For any lottery a, continuity guarantees a unique weight λ with
a ≈ (λ·best + (1−λ)·worst); define u(a) = λ. Mixing builds a *thermometer*
between two reference states, and independence guarantees the readings
transport consistently to all comparisons. Every representation proof has
this skeleton somewhere.
*Here:* with cmix the thermometer survives verbatim — REP rides on it. With
smix, the "scale" between two fixed states is not a segment but a sphere
(weight × relative phase — see cmix vs smix), a *2-dimensional*
thermometer. That is precisely why a single real-valued utility is no
longer forced, and why LEX and XTERM are live targets.

### Independence axiom
If you prefer b to a, you must prefer "λ chance of b, else c" to "λ chance
of a, else c" — mixing both sides with the same third option can't flip a
ranking. The most attacked classical axiom (Allais paradox), and the one
quantum mechanics threatens *structurally*: a quantum "third option" can
interfere with the things being compared.
*Here:* 2c/SAFEIND keeps only a restricted "safe zone" of independence
(third option orthogonal to both). But see *interference cross-term* below
for why "orthogonal = safe" is subtler than it sounds.

### Continuity / closed graph
"No infinitely good or bad options": small perturbations of states don't
flip strict preferences. The clean topological form: the set of pairs
{(a,b) : a ≼ b} is closed — limits of preferences are preferences.
*Here:* S1/CLOSED in `Base.lean`. In the representation proof it's what
upgrades "linear on nice subsets" to "continuous linear functional."

### Mixture space
An abstract structure where any two elements can be mixed with a weight λ,
subject to natural laws (Mongin 2001, in `papers/`). Lotteries form one;
so do density matrices under classical mixing. State *vectors* under
superposition do **not** quite — normalization fails for non-orthogonal
pairs (see cmix vs smix).
*Here:* `MixingStructure` in `Mixing.lean` generalizes this; deciding which
laws survive for superposition-mixing is open thread A01.

### Money pump / Dutch book
An exploitation argument: if your preferences have a certain bad structure
(a cycle, a non-monotonicity), an adversary can offer you a sequence of
trades, *each acceptable by your own lights*, that returns you to where you
started minus resources. Repeatable, so you can be drained. Standard
justification for axioms: "violate this and you're pumpable."
*Here:* motivates NMP (measure pump) and C1/COHUP (Mach–Zehnder pump).
Open thread: the adversary's "trades" are *operations*, which our formalism
doesn't yet contain — see the NoPump schema (A07).

### Simplex; unique decomposition ★
The lottery space is a *simplex*: the corners are the sure outcomes, and —
the crucial property — **every point is a mixture of corners in exactly one
way**. A 50/50 coin is the midpoint of heads and tails, and there is no
other recipe for it. Simplices are precisely the convex sets with this
uniqueness. Hold this thought; its failure is the deepest thing in Part II.
*Here:* "classical = simplex" is the structural meaning of "classical" in
this project.

---

## Part II — Quantum states, slowly

### Amplitude, superposition
Where a lottery attaches a probability pᵢ to outcome i, a quantum state
attaches a complex *amplitude* αᵢ; the probability of seeing i is |αᵢ|².
A *superposition* α|0⟩ + β|1⟩ is not "secretly 0 or 1 with probabilities" —
it's a genuinely different kind of object, and experiments (interference)
can tell the difference. An amplitude carries two real numbers (magnitude
and phase) where a probability carries one; that extra phase is where all
the new phenomena hide.
*Here:* the founding move — "what if preferences range over these instead
of lotteries?"

### Born rule
The bridge from amplitudes back to lotteries: measuring in a basis yields
outcome i with probability |αᵢ|². Every quantum state *induces* a classical
lottery per measurement context.
*Here:* the trapdoor. If preferences only see the induced lottery (axiom
E1/BORNTRAP), the whole project collapses back to vNM — deliberately not
adopted. "How much more than the Born lottery can preferences see?" is the
research question.

### The two trapdoors: Born ≠ vNM
Factoring preferences through Born statistics has two separate floors, and
falling through the first does not drop you through the second.
**Floor 1 (Born-collapse):** preferences depend only on the Born lottery.
But in *which basis*? Knowing the Born statistics for **every** measurement
is the same as knowing the density matrix — that is B1/OPEQ, fully quantum,
no collapse at all. Collapse only happens when one *fixed* basis is
privileged (pointer-justified, or else poison P-GRID).
**Floor 2 (vNM-collapse):** even inside lottery-land, expected utility
needs vNM's own axioms — completeness, continuity, and above all
*independence*. Without independence, non-EU lottery preferences abound:
rank-dependent weighting, variance aversion, worst-branch caution.
*Here:* "back to Born but not back to vNM" is a coherent, live position —
an Everettian with non-linear risk attitudes over branch measure. The
Deutsch–Wallace program claims rationality forces both floors; its critics
attack exactly the second fall (threads D02, D07). Guard P-TRAP floor by
floor.

### Phase: global vs relative
Multiplying an entire state by e^{iθ} (global phase) changes nothing
physical — no experiment can detect it. Changing the phase *between*
components is different: (|0⟩+|1⟩)/√2 and (|0⟩−|1⟩)/√2 are distinct,
perfectly distinguishable states. Relative phase is physics; global phase
is bookkeeping.
*Here:* S2/GPHASE demands indifference to global phase only (mandatory
hygiene). 4c/DIAL demands indifference to *per-component* phases — vastly
stronger, erases all interference structure, hence its ⚠.

### Ray; gauge; projective space
A state vector ψ and its scalar multiple e^{iθ}ψ describe the same physical
situation; the physical object is the *ray* (the line through ψ), and the
space of rays is *projective Hilbert space*. Choosing one particular vector
on the ray is a *gauge choice* — bookkeeping, like choosing where zero
longitude sits. Anything defined on vectors that doesn't descend to rays is
gauge-dependent and therefore not yet physics.
*Here:* S2/GPHASE is the axiom-level echo ("preferences descend to rays").
The smix well-definedness problem (see cmix vs smix) is gauge-dependence
biting: superposition is an operation on *vectors*, not on rays. Density
matrices solve the gauge problem wholesale — part of B1/OPEQ's appeal.

### Orthogonality
⟨ψ|φ⟩ = 0: the states are perfectly distinguishable by some single
measurement. The classical analog is lotteries with disjoint support.
⚠ Warning that recurs throughout: orthogonal states can still "interact"
inside a *valuation* — see interference cross-term.
*Here:* the `Orthogonality` class; the guard rail in 2c/SAFEIND.

### Basis; measurement context
A maximal set of mutually orthogonal states = one complete way of asking
"which outcome?" Quantum mechanics has *many incompatible* bases for the
same system (Z-spin vs X-spin; position vs momentum) — that plurality is
the raw material for interference, contextuality, and most of Part III.
*Here:* an axiom that privileges one basis without physical justification
commits poison P-GRID ("caring about coordinates").

### Observable (Hermitian operator); expectation value
The quantum encoding of a measurable quantity: a matrix Ô equal to its own
conjugate-transpose (*Hermitian* / *self-adjoint*). Its eigenvalues are the
possible measured values; its eigenvectors are the states having that value
definitely. The *expectation value* ⟨ψ|Ô|ψ⟩ — or Tr(ρÔ) for density
matrices — is the average over many measurements. Note the shape: quadratic
in amplitudes, *linear* in the density matrix.
*Here:* target #1/OBS says the utility function of a rational quantum agent
*is* an observable Û, with preference = expectation ordering.

### Density matrix (ρ); pure vs mixed
The operational state: a PSD (see below), trace-1, Hermitian matrix
packaging *everything any measurement could reveal* about a system. A
*pure* state ρ = |ψ⟩⟨ψ| is maximal knowledge; a *mixed* state is a classical
probability blend of pure ones. Diagonal entries = Born probabilities in
that basis; off-diagonal entries = coherence (below).
*Here:* `DensityMatrix` in `Qubit.lean`; B1/OPEQ is the axiom that
preferences live here rather than on state vectors.

### Ensemble non-uniqueness ★
The single deepest difference from the classical world. Recipes:
"50/50 of |0⟩ and |1⟩" and "50/50 of |+⟩ and |−⟩" produce **the same
density matrix** — and no experiment whatsoever can tell which recipe was
used. A classical mixed state has exactly one decomposition into pure
outcomes (the simplex property); a quantum mixed state has *infinitely
many*. The quantum state space is a round convex body, not a simplex —
for one qubit, literally a ball.
*Here:* (1) B1/OPEQ forces indifference across same-ρ recipes — a strong,
purely quantum commitment with no classical counterpart; (2) the failure of
unique decomposition is *why* per-basis classical reasoning doesn't glue
into a global utility for free, and why Gleason's theorem (Part III) is
needed where classically vNM sufficed.

### Entanglement; partial trace; purity ★
Put two systems together and the joint states live in the *tensor product*
of their spaces. A pure joint state like the Bell state (|00⟩+|11⟩)/√2
assigns **no pure state to either half**. "What does Alice's half look like
on its own?" is answered by the **partial trace**: average the other system
out. For the Bell state, Alice's reduced state is I/2 — maximally mixed,
indistinguishable from a fair coin — even though the pair as a whole is in
a state of maximal knowledge. Moral: *mixedness of a part measures
entanglement with the rest.* This is the second, deeper source of density
matrices (the first was ignorance of recipe): they are forced on you,
because pure states are not closed under "look at a subsystem."
**Purity** Tr(ρ²) quantifies it — 1 for pure, 1/n for maximally mixed; the
radial coordinate of the Bloch ball. Decoherence in this language: the
environment entangles with the system, and the system's reduced ρ loses its
off-diagonals in the pointer basis. The phases are not destroyed — they are
*exiled* into system–environment correlations that no local measurement can
reach.
*Here:* the missing tensor structure is the biggest structural gap in the
toolkit (R1/ANCILLA, the Bell axiom A04, and decoherence all need it).
Everett reading: branches = diagonal blocks of the post-decoherence reduced
ρ, measure = their weights. Quantum-computing reading: a computation is a
fight to keep ρ pure.

### Spectral decomposition
Every density matrix can be written ρ = Σ λᵢ|eᵢ⟩⟨eᵢ| with the eᵢ mutually
orthogonal and λᵢ ≥ 0 summing to 1 — "diagonalize it." Among the infinitely
many ensemble recipes for ρ, this is the canonical *orthogonal* one.
*Here:* the headline proof sketch runs through these: 2c-style independence
applied to spectral mixtures gives per-basis linearity, and then the gluing
problem starts.

### PSD (positive semidefinite); utility floor
A Hermitian matrix is PSD when all eigenvalues are ≥ 0, equivalently
⟨ψ|Ô|ψ⟩ ≥ 0 for every state — "the quantity is never negative." For a
utility observable, PSD (modulo affine shift) means *utility is bounded
below* — there's a worst it can get, a vacuum.
*Here:* TH05/VACUUM. We learned the hard way (retired sign-blind NMP) that
this should come from an explicit floor axiom (NIW), not fall out of a pump
argument.

### Bloch ball
The geometry that makes one qubit visualizable: density matrices of a qubit
↔ points of the solid unit 3-ball. Surface = pure states; center = the
maximally mixed state; antipodal surface points = orthogonal pure states;
the spectral decomposition of an interior point = the unique diameter
through it. Classical mixing = straight-line interpolation.
*Here:* where the n=2 pathologies become pictures: a "frame function"
counterexample is just a function on the ball, linear along every diameter
but not globally linear (e.g. u = r_z³/|r|²).

### Trace; trace duality
Tr(M) = sum of diagonal entries. The pairing ⟨A,B⟩ = Tr(AB) makes Hermitian
matrices into a real inner-product space — which means: **every linear
functional on density matrices is Tr(·Ô) for exactly one Hermitian Ô.**
Linear valuations and observables are the same thing in different clothes.
*Here:* the last step of TH01/REP. Once axioms force preferences to be
linear in ρ, the utility observable Û pops out by duality, for free. All
the work is in getting to "linear."

### Subnormalized states; the cone
Relax "trace = 1" to "trace ≤ 1": a state that only obtains with weight
t < 1 — a branch that might not happen, a post-selection that might fail.
Geometrically you pass from the convex body to the *cone* over it, with the
zero state ("nothing survives") at the tip.
*Here:* double duty: (1) `HasMeasure`/NMP are vacuous on trace-1 states
(measure is constantly 1) and only bite on the cone; (2) superposition of
non-orthogonal normalized states isn't normalized, so smix (below) is only
a total operation on the cone. One structural move, two problems solved.

### Decoherence; pointer basis
Interaction with an environment rapidly kills the off-diagonal entries of ρ
*in a particular basis* selected by the physics of the interaction (the
*pointer basis*) — turning superpositions into effective classical
mixtures. This is how the classical world emerges, and it's the one
physically legitimate way a "preferred basis" enters.
*Here:* E2/POSTCLASS speaks only about already-decohered states. The
pointer basis is the single allowed exception to poison P-GRID — and any
axiom using it must say so explicitly.

### Coherence
Having nonzero off-diagonal density-matrix entries in a given basis — the
resource that powers interference. Modern quantum information treats it as
a formal resource (resource theory of coherence, thread D03), with
monotones measuring "how much."
*Here:* C1/COHUP demands preferences be monotone in some coherence measure;
target #2/BONUS wants utility = classical EU + a coherence bonus.

### Interference cross-term ★
Value a superposition αa + γc with an observable Ô and you get
|α|²·(a's value) + |γ|²·(c's value) **+ 2Re(ᾱγ⟨a|Ô|c⟩)** — a third term
belonging to neither component. ⚠ The trap: ⟨a|Ô|c⟩ can be nonzero *even
when a and c are orthogonal*. Distinguishability of states does not mean
non-interaction inside a valuation; the cross-term lives off the diagonal
of Ô, not in the overlap of the states.
*Here:* why 2c/SAFEIND's motto "orthogonal = interference-free" is false at
the state-vector level (it's fine for classical mixing of density
matrices); and the seed of target #5/XTERM, where the cross-term becomes
its own utility channel.

### cmix vs smix; coherence premium ★ (our coinage)
Two genuinely different ways to "mix" quantum states, which the classical
world cannot distinguish because it only has the first:
**cmix** — classical/convex mixture of density matrices: λρ + (1−λ)σ.
A decohered ensemble; no interference; this is lottery-mixing.
**smix** — superposition with complex weights: αψ + γφ. Interference; needs
the cone (or orthogonality) to even be well-defined.
The **coherence premium** of a superposition is then definable:
u(smix) − u(cmix with the matching Born weights) — how much the agent
values the coherent version *over* its decohered shadow. E1/BORNTRAP is
exactly "the premium is always zero."
⚠ Deeper problem (2026-06-12): smix is not even well-defined on *physical*
states. ψ and e^{iθ}ψ are the same physical state, yet αψ + βφ and
αe^{iθ}ψ + βφ are *different* physical states — superposing two states
requires choosing representatives (a gauge). The honest parameterization is
weight λ = |α|² **plus a relative phase** θ. Qubit picture: cmix of |0⟩ and
|1⟩ sweeps a segment (the vertical diameter of the Bloch ball); smix sweeps
the whole sphere *surface* — weight is the latitude, relative phase the
longitude. The quantum rescue of "summing lotteries" inflates the interval
[0,1] into interval × circle. Any axiom quantifying over smix must
quantify over the phase too, or demand phase-covariance.
*Here:* proposed refactor of `MixingStructure` (thread A06); makes targets
#2/BONUS and #5/XTERM crisply statable.

### Everettian measure
In many-worlds thinking, the squared amplitude of a branch — read not as
"probability that it happens" (they all happen) but as "how much that
branch *counts*." How a rational agent should weight branches by measure is
the Deutsch–Wallace research program (thread D02).
*Here:* `HasMeasure` and the NMP family. The "I hate that branch, shrink
it" insight that made NMP sign-aware lives here.

---

## Part III — The heavy machinery

### Frame function; Gleason's theorem ★
A *frame function* assigns a number to each pure state such that every
orthonormal basis sums to the same constant — "additivity across each
measurement context." **Gleason (1957):** in dimension ≥ 3, every such
(bounded) function is Tr(ρ·)-shaped — context-wise additivity *forces*
global linearity. This is the engine that turns per-basis classical
reasoning into a single quantum representation; it's how the gluing problem
from *ensemble non-uniqueness* gets solved.
**The catch:** in dimension 2 it is **false**. A qubit's pure state belongs
to only one basis (itself and its antipode), so the additivity constraint
is far too weak — any odd function on the Bloch sphere yields a
counterexample.
*Here:* TH01/REP is Gleason in decision-theoretic clothing, so it needs
n ≥ 3 — the qubit flagship is the one pathological dimension (poison
P-EDGE). Hence: promote the qutrit, or take the POVM route below.

### POVM; Naimark dilation; Busch's theorem
Projective measurements (measure in an orthogonal basis) are not the most
general thing quantum mechanics allows. The general notion is a **POVM**;
operationally: adjoin an auxiliary system (*ancilla*), evolve jointly,
measure the ancilla projectively. **Naimark dilation** says every POVM
arises this way. **Busch (2003):** Gleason's conclusion for POVMs holds in
*every* dimension, including 2 — the extra measurements supply the missing
constraints.
*Here:* the possible rescue of the qubit flagship: R1/ANCILLA + B1 on
system⊗ancilla is morally "preferences respect POVM statistics," which is
Busch's hypothesis. The recipe for target #1 listed R1 before we knew why
it was load-bearing.

### Unitary; channel (CPTP map)
What can *happen* to a quantum state. A **unitary** is reversible
evolution — a rotation of state space, no information lost, pure states to
pure states. A **channel** (CPTP map) is the most general physically
allowed transformation: unitaries, adjoining ancillas, measuring,
forgetting — including irreversible processes like decoherence. Stinespring
(sibling of Naimark): every channel is a unitary on a larger system
followed by ignoring part of it. Classical analog: stochastic matrices
acting on lotteries.
*Here:* the toolkit currently has states but no transformations. The
operations layer (thread A07) would add channels-with-costs, making Dutch
books finally statable (P-PUMP), unifying the pump axioms, and offering
"mixing as a process" (a beamsplitter channel) as a third reading of
mixing — see cmix vs smix.

### GPT (generalized probabilistic theory)
A framework where a physical theory is reduced to: a convex state space +
affine functionals as measurements. Classical probability = the simplex;
quantum = the density-matrix body; the *rebit* (real amplitudes, thread
I01) = a disk; exotic theories in between. Useful because it isolates
*which* quantum features come from convex geometry alone.
*Here:* the toolkit is secretly decision theory over a GPT. In GPT terms,
"linear preferences = dual-cone element" is automatic convex duality — so
target #1/OBS is the sanity check, and the genuinely quantum decision
theory lives where linearity *fails* or *underdetermines* (#3, #5, #6,
n=2).

### Contextuality (Kochen–Specker)
The impossibility of assigning definite values to all quantum observables
at once, consistently across overlapping measurement contexts. Values exist
only *relative to a context*.
*Here:* target #3/CTX is its decision-theoretic shadow: per-context utility
with no global utility function. Note it *requires* dropping B1/OPEQ —
context-dependence is exactly preference over distinctions that operational
statistics don't make.

---

## Slug tables

### Axioms

| Tag | Slug      | Lean class                       | One line                                                  |
|-----|-----------|----------------------------------|-----------------------------------------------------------|
| —   | REFL      | `IsReflexive`                    | every state at least as good as itself                    |
| —   | TRANS     | `IsTransitive`                   | preference chains compose                                 |
| S1  | CLOSED    | `HasClosedGraph`                 | limits of preferences are preferences                     |
| C2  | CLIND     | `HasClosedIndifference`          | indifference classes are closed                           |
| S2  | GPHASE    | `IsInvariantUnder`               | global phase is invisible                                 |
| 2a  | FLATTEN   | `CompoundReduction`              | compound mixtures flatten (placeholder, A01)              |
| 2b  | WEIGHT    | `MonotoneOwnWeight`              | more weight on the better branch is better                |
| 2c  | SAFEIND   | `OrthogonalIndependence`         | independence in the orthogonal "safe zone" ⚠ subtle       |
| 4a  | SHUFFLE   | `PermutationInvariant`           | outcome labels don't matter ⚠ stronger than it looks      |
| 4c  | DIAL      | `PerOutcomePhaseInvariant`       | per-branch phases don't matter ⚠ erases interference      |
| C1  | COHUP     | `MonotoneInCoherence`            | more coherence is never worse                             |
| C3  | WALK      | `HasConnectedIndifference`       | you can walk within an indifference class                 |
| C4  | SHEET     | (deferred)                       | indifference classes are hypersurfaces                    |
| B1  | OPEQ      | `RespectsOperationalEquivalence` | same measurement stats ⇒ indifferent                      |
| E1  | BORNTRAP  | (deliberately not adopted)       | superposition ≈ its Born mixture — the classical trapdoor |
| E2  | POSTCLASS | `PostDecoherenceClassical`       | classical EU after decoherence                            |
| R1  | ANCILLA   | `AncillaInvariant`               | environment-only operations are invisible                 |
| NMP | NMP       | `NoMeasurePump{Weak,Strict}`     | shrinking measure moves you toward null (sign-aware)      |
| MI  | RENORM    | `MeasureIndifference`            | only the ray matters; measure is bookkeeping              |
| NIW | NIW       | `NullIsWorst`                    | "nothing" is the worst state (explicit floor)             |

### Targets (`Qtility/Targets.lean`)

| #  | Slug  | Name                        | One line                                          |
|----|-------|-----------------------------|---------------------------------------------------|
| 1  | OBS   | Observable-valued utility   | utility is a self-adjoint operator                |
| 2  | BONUS | Coherence axis              | utility = Born-EU + coherence bonus               |
| 3  | CTX   | Contextual utility          | per-context utility, no global one                |
| 4  | LEX   | Lexicographic utility       | vector utilities, ordered lexicographically       |
| 5  | XTERM | Interference-as-information | the cross-term is its own utility channel         |
| 6  | NOREP | No representation           | provably no single-function representation        |

### Theorem threads (`NEXT.md`)

| Tag  | Slug   | One line                                            |
|------|--------|-----------------------------------------------------|
| TH01 | REP    | the representation theorem (axioms ⇒ observable)    |
| TH02 | FWD    | observables satisfy the axioms (converse direction) |
| TH03 | AFFU   | affine uniqueness (Û pinned up to aÛ + bI)          |
| TH04 | CLREC  | classical recovery on demand (trapdoor confirmed)   |
| TH05 | VACUUM | explicit floor axiom ⇒ PSD utility observable       |

### Poisons (`Qtility/Poisons.lean`)

| Slug   | One line                                                       |
|--------|----------------------------------------------------------------|
| P-BOOM | contradiction — the axiom bundle has no model at all           |
| P-MUSH | triviality — only degenerate preferences survive               |
| P-FLOP | floppiness — representation exists but isn't pinned down       |
| P-TRAP | classical trapdoor — secretly forced back to Born/vNM          |
| P-GRID | coordinate worship — privileging a basis without physics       |
| P-SMUG | smuggling — the conclusion was hiding inside an axiom          |
| P-VOID | vacuity — an axiom whose hypothesis never fires                |
| P-EDGE | edge-dimension fragility — true only at special n              |
| P-PUMP | exploitability — an open Dutch book survives the axioms        |
