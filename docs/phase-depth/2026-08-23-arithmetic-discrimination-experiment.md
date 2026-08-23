# Phase 4 — Canonical arithmetic phase-depth cocycle: a discrimination experiment

**Status: COMPUTATION (empirical), not PROVED.** This is a designed experiment over real prime
data, reported honestly — it is *not* a Lean theorem and is deliberately kept out of the PROVED
registry. Reproducible via `experiments/phase-depth/*.py` (primes to 10⁸, pure sieve + NumPy).

## The question (from the program's north star)
The formal spine proves that the pentagon transfer operator's trace spectrum is governed by the
fiber holonomy `H` and is invisible to the residue (mod-5) marginal — i.e. to first-order Fourier
data (`Brockian.PhaseDepthTransfer`, `PhaseDepthTraceMatrix`, `DepthHolonomySeparation`). Phase 4
asks the decisive research question: when the cocycle is built from **actual arithmetic data with no
tunable weights**, does the holonomy carry information that ordinary residue statistics do not — or
is it a sharp no-go?

## The canonical cocycle (no free parameters)
Primes `p > 5` have residues `r_n = p_n mod 5 ∈ {1,2,3,4}` (the units). Everything below is
determined by the prime sequence alone:
- **roof / seam weights** = the actual consecutive prime residues `r_n` (no chosen weights);
- over each non-overlapping window of 5 consecutive primes, two natural phase-depth invariants:
  - **holonomy** `H_k = (∑_{j} r_{5k+j}) mod 5` (total depth of the window),
  - **depth** `D_k = #{ j : r_{5k+j+1} = r_{5k+j} }` (consecutive repeats — the phase-depth
    accumulation; the Lemke Oliver–Soundararajan phenomenon predicts repeats are *suppressed*).

At 10⁸ the marginals are perfectly equidistributed (≈ 1.15M windows; each residue ≈ 25.0%), so any
signal lives entirely in the *correlations*, exactly where phase-depth is meant to look.

## The test: match the null to ever-higher residue correlations
We compare the real holonomy/depth distribution against the **exact** prediction of a `k`-th order
Markov model fitted to the primes — the model that reproduces all residue correlations up to
`(k+1)` points, and nothing higher. If the holonomy still deviates after matching order `k`, it sees
beyond `(k+1)`-point statistics; if the deviation vanishes, it does not.

### Result — depth `D` (repeat count), 1,152,290 windows

| null matches correlations up to | TV(real, null) | χ² (dof 4) | p |
|---|---|---|---|
| **pairwise** (Fourier / 1-step) | **0.01056** | 936.1 | 2.5 × 10⁻²⁰¹ |
| triples (2-step) | 0.00089 | 13.5 | 8.9 × 10⁻³ |
| 4-point (3-step) | 0.00084 | 9.3 | 5.4 × 10⁻² (n.s.) |
| 5-point (4-step) | 0.00026 | 0.8 | 0.94 |

(The holonomy `H = ∑ mod 5` behaves identically: TV 0.00339 vs the pairwise null, χ² = 86, and it
too collapses under higher-order matching.)

## Verdict — a sharp bounding (near-no-go)
1. **Does the holonomy distinguish beyond residue statistics?** *Beyond first-order, yes; beyond
   low-order, no.* It deviates enormously from a pairwise-matched null (p ≈ 10⁻²⁰¹) — a genuine
   detection of the beyond-Fourier Lemke Oliver–Soundararajan correlation. But **matching just the
   3-point correlations absorbs ~92 % of that deviation** (TV 0.0106 → 0.00089), and 4-point matching
   renders the residual statistically insignificant. The construction carries essentially **no
   arithmetic information beyond ≤ 3-point residue correlations**.
2. **Stable under the natural symmetries?** *Yes.* Reversing window orientation leaves the holonomy
   distribution invariant (χ² = 0, p = 1) — the empirical counterpart of the proved
   `PhaseDepthD5.totalDepth_reflection_invariant` (a plain sum is reflection-invariant; only the
   *directed* holonomy sees orientation).
3. **Does it correlate with a meaningful quantity?** *Yes.* The entire signal is the L-O–S
   consecutive-residue bias (repeat suppression: repeat-probabilities ≈ 0.16–0.18 vs uniform 0.25),
   a documented arithmetic phenomenon captured by the Hardy–Littlewood `k`-tuple heuristics.

**Where the next construction must change.** This canonical additive residue-window cocycle is, to
within TV < 0.001, a *functional of the low-order residue-correlation structure* — it re-expresses
information already accessible to standard k-tuple/Fourier analysis rather than exceeding it. To
carry genuinely new arithmetic content, the phase-depth cocycle must be built from data that is
**not** a low-order residue statistic — e.g. multiplicative/character or spectral (zero-statistic)
input, or a branched construction whose fiber holonomy is not determined by short-range residue
correlations. That is the concrete redirection this negative result buys.

## Honest scope
- Empirical, primes ≤ 10⁸, one canonical construction and two natural statistics. It does not prove
  a no-go for *all* phase-depth constructions; it sharply bounds *this* one.
- The order-4 consistency (p = 0.94) is partly tautological (a 5-window statistic is a function of
  its 5 residues) and serves as a correctness check on the machinery; the content is the *early*
  saturation at order 2–3.
- Reproduce: `python3 experiments/phase-depth/phase4_saturation.py` (and `_exact_null.py`,
  `_discriminate.py`, `_cocycle.py`).
