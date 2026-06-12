# Expected Utility Theorem — primary sources

Reference set for the vNM expected-utility representation theorem: given a preference relation `≤` on lotteries satisfying completeness, transitivity, continuity, and independence, there exists a utility function `u` on outcomes such that `L ≤ L'  ⇔  E[u | L] ≤ E[u | L']`, unique up to positive affine transformation.

Organized as: the **original** (1947), the **classical reformulations** (1950–1967), **structural variants** (drop an axiom), **modern syntheses**, and **formalized / constructive** treatments.

## The original

### `1947-vnm-theory-of-games.pdf` — von Neumann & Morgenstern, *Theory of Games and Economic Behavior*, 2nd ed.

The proof everyone calls ugly. The four axioms are stated in §3.6.1 (Ch. I). The construction itself is the **Appendix: "The Axiomatic Treatment of Utility"**, starting at §A.1 — von Neumann calibrates an arbitrary lottery against best/worst reference lotteries by a Dedekind-cut-style halving argument. He apologizes for the construction's clunkiness in the appendix's own introduction.

The PDF is a scanned image (no embedded text). `1947-vnm-theory-of-games-OCR.txt` is the archive.org djvu OCR; the appendix text begins at byte offset 1,724,818 (search for `AXIOMATIC TREATMENT OF UTILITY`).

Source: archive.org/details/in.ernet.dli.2015.215284 (Digital Library of India scan of a printing carrying prefaces to both the 2nd and 3rd editions; the appendix is unchanged from 1947).

## Classical reformulations (1950–1967)

### `1950-nash-bargaining-problem.pdf` — Nash, *Econometrica* 18(2), 155–162.

Often overlooked: Nash gave an independent axiomatization of expected utility in §2 of this paper, simultaneously with Marschak in the same April-1950 issue of *Econometrica*. Both were the first to state the **independence axiom** explicitly (vNM had used it implicitly). Source: Haverford College.

### Marschak, "Rational Behavior, Uncertain Prospects, and Measurable Utility," *Econometrica* 18(2), 111–141 (1950) — **not included; JSTOR-only**.

Stable URL: https://www.jstor.org/stable/1907264. The other co-discoverer of the independence axiom; gives a more economist-friendly exposition than Nash. Precursor: Cowles Commission Discussion Paper, Economics #226 (1948), hectographed — not in elischolar.

### Herstein & Milnor, "An Axiomatic Approach to Measurable Utility," *Econometrica* 21(2), 291–297 (1953) — **not included; JSTOR-only**.

Stable URL: https://www.jstor.org/stable/1905540. **This is the canonical "elegant" reproof.** Replaces vNM's combinatorial calibration with the abstract notion of a *mixture set* (a set with a binary operation `(p, x, y) ↦ x⊕_p y` satisfying three algebraic identities) and uses a clean continuity argument. Most modern textbook proofs descend from this one.

### Jensen, "An Introduction to Bernoullian Utility Theory I: Utility Functions," *Swedish J. of Economics* 69, 163–183 (1967) — **not included; journal-paywalled**.

Reduces the axiom set to weak order + independence + Archimedean — widely cited as the **minimal-axiom version**.

## Structural variants (drop an axiom)

### `1952-hausner-multidimensional-utilities-rand.pdf` — Hausner, RAND P-336.

The preprint of "Multidimensional Utilities," published in Thrall, Coombs & Davis (eds.), *Decision Processes*, Wiley 1954. Drops the **Archimedean** condition and gets a lexicographic vector-valued utility instead of a scalar one. Embedded in an ordered vector space rather than ℝ. Source: DTIC.

### `1962-aumann-utility-without-completeness.pdf` — Aumann, *Econometrica* 30(3), 445–462, plus the 1964 correction.

Drops the **completeness** axiom. Gets a partial-order representation: there's still a utility function, but its expected value gives a necessary-not-sufficient condition for preference; preferences satisfying the other axioms can be richer than EU comparison. Important precursor to the modern literature on incomplete preferences. Single PDF includes the 1964 correction (*Econometrica* 32(1–2), 210–212).

## Modern syntheses

### `2001-mongin-mixture-set-DEF.pdf` — Mongin, *Decisions in Economics and Finance* 24, 59–69.

Short, modern reconstruction of the mixture-set approach. Useful as a recent re-exposition of Herstein-Milnor when you don't have JSTOR access — Mongin re-derives the core representation theorem with cleaner machinery.

## Diverse modern treatments

### `2012-arxiv-common-math-foundations-eu-dual.pdf` — Dyckerhoff & Mosler (arXiv 1211.4469).

Unifies vNM expected utility and Yaari's dual utility in a common axiomatic framework — useful for seeing what's specifically "linear in probabilities" versus "linear in outcomes."

### `2018-arxiv-completeness-transitivity-mixture-sets.pdf` — Schlee et al. (arXiv 1810.02454).

What happens when you weaken both completeness and transitivity on mixture sets. Maps out the lattice of axiom weakenings.

### `2021-arxiv-eu-mixture-spaces-no-completeness.pdf` — McCarthy & Mikkola (arXiv 2102.06898).

Modern descendant of Aumann 1962: a cleaner construction of EU on mixture spaces when completeness is dropped, using more recent functional-analytic tools.

### `2022-arxiv-continuity-postulates-solvability.pdf` — Khan, Pivato et al. (arXiv 2202.08415).

Consolidates the continuity/Archimedean/solvability conditions across vNM, mathematical psychology (measurement theory), and topology. Useful for understanding why the "continuity" axiom can be formulated so many ways.

## Formalized / constructive

These are the most directly relevant to this repo's formalization effort
(now Lean 4 + Mathlib; originally Agda — see `agda-archive/`).

### `2023-arxiv-expected-utility-constructive.pdf` — Steinerberger (arXiv 2303.08633).

**Read first if formalizing in a constructive proof assistant.** Re-examines vNM from a constructive viewpoint — which steps are computational, which need classical logic / choice, where the existence claims can be replaced by witness-producing constructions.

### `2025-arxiv-lean4-vnm-formalization.pdf` — Zhang et al., "From Axioms to Algorithms" (arXiv 2506.07066).

**The state of the art in mechanized proofs of the vNM theorem.** Lean 4 + Mathlib formalization of the four axioms and the representation theorem. Worth reading even if you stay in Agda — for axiom encoding choices, choice-of-base-utility scaling, and what they had to add to Mathlib.

## Quantum side — wanted (not yet fetched)

The 2026-06-12 review identified these as load-bearing for the quantum
half of the project; none are in the folder yet.

- **Gleason 1957**, "Measures on the closed subspaces of a Hilbert space,"
  *J. Math. Mech.* 6, 885–893. The engine behind TH01/REP; fails at n = 2.
  No arXiv version (pre-print era); university course sites often host scans.
- **Busch 2003**, "Quantum states and generalized observables: a simple
  proof of Gleason's theorem," *PRL* 91, 120403 — arXiv quant-ph/9909073.
  The POVM version; holds in all dimensions, rescuing the qubit.
- **Barrett 2007**, "Information processing in generalized probabilistic
  theories" — arXiv quant-ph/0508211. GPT framework; anchors the rebit
  instance (I01).
- **Baumgratz, Cramer, Plenio 2014**, "Quantifying coherence" —
  arXiv 1311.0275. Resource theory of coherence; grounds C1/COHUP and
  target BONUS (thread D03).
- **Deutsch 1999**, "Quantum theory of probability and decisions" —
  arXiv quant-ph/9906015. Start of the Deutsch–Wallace program (D02);
  directly relevant to the two-trapdoors question (D07).
- **Wallace 2012**, *The Emergent Multiverse*, OUP — book, not freely
  available; his earlier arXiv papers (e.g. quant-ph/0303050) cover the
  decision-theoretic core.

## Paywalled — canonical URLs

Three classical reformulations are JSTOR-only and not redistributable. If you have institutional access:

- **Marschak 1950** — https://www.jstor.org/stable/1907264
- **Herstein–Milnor 1953** — https://www.jstor.org/stable/1905540
- **Jensen 1967** — Scandinavian Journal of Economics (formerly Swedish J. of Economics), vol. 69, pp. 163–183

Mongin 2001 (above) is the best open-access stand-in for Herstein–Milnor.
