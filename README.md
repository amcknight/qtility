# qtility

What happens to decision theory when classical lotteries become quantum
superpositions — formalized in Lean 4 + Mathlib.

The founding observation: a lottery (nonnegative reals summing to 1) and a
quantum state (complex amplitudes whose squared norms sum to 1) are
mathematically adjacent. Classical decision theory (von Neumann–
Morgenstern) turns preference axioms over lotteries into a scalar utility
function, unique up to affine rescaling. What do preference axioms over
quantum states turn into? An observable? Something stranger?

Rather than committing to one axiom system, this repo is an **axiom
toolkit**:

- a catalog of independently adoptable **axioms**, each motivated by a
  physical principle or thought experiment (operational equivalence,
  decoherence, Mach–Zehnder Dutch books, Everettian measure, …);
- a catalog of **targets** — results we'd like specific axiom bundles to
  land (utility as a self-adjoint operator, coherence as a utility axis,
  contextual utility, interference as its own utility channel, …);
- a catalog of **poisons** — failure modes any bundle must avoid
  (contradiction, triviality, smuggled conclusions, secret classicality,
  coordinate worship, …).

## Orientation

| File | What it is |
|---|---|
| `GLOSSARY.md` | living concept reference + slug tables — start here |
| `NEXT.md` | active threads, pick-up-able by a fresh session |
| `Qtility/Targets.lean` | the targets catalog (slugs: OBS, BONUS, CTX, LEX, XTERM, NOREP) |
| `Qtility/Poisons.lean` | the poisons catalog (P-BOOM … P-PUMP) |
| `Qtility/Base.lean` | floor axioms: preference relation, continuity, phase invariance |
| `Qtility/Mixing.lean` | mixing structures + independence-family axioms |
| `Qtility/Symmetry.lean` | permutation / per-outcome-phase axioms (mutually trivializing ⚠) |
| `Qtility/Continuity.lean` | stronger continuity options |
| `Qtility/PhysicalAxioms.lean` | physics-grounded axioms: operational equivalence, decoherence, measure pumps, coherence monotonicity |
| `Qtility/Instances/` | concrete state spaces: classical lotteries, density matrices |
| `papers/` | reference papers, indexed in `papers/README.md` |
| `agda-archive/` | the original Agda experiment, kept untouched |

## Status

Exploratory. The axiom toolkit and two instances (classical `Lottery`,
quantum `DensityMatrix`) compile; most axiom verifications and all theorem
threads are open. The headline target (OBS: axioms ⇒ utility is a
self-adjoint operator, via a Gleason-style argument + trace duality) is
stated with known caveats — see TH01/REP in `NEXT.md`.

## Build

```
lake build
```

Lean toolchain and Mathlib version are pinned in `lean-toolchain` /
`lakefile.toml`.
