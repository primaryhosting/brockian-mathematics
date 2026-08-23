# Movement D — the Frobenius escape: verdict

**Status: COMPUTATION (empirical), not PROVED.** Reproducible via
`experiments/phase-depth/phase4D_rigorous.py` (train/test split; null fit on one half, χ²/TV
measured on the held-out half). This tests the plan's central hope — that **non-abelian /
multiplicative** arithmetic data (Frobenius symbols in a Galois extension) would carry the
higher-order correlation that the additive residue cocycle lacked (Phase 4's near-no-go).

## The test
For a Galois quintic, the Frobenius at an unramified prime `p` is the factorization type of the
polynomial mod `p` (its cycle type as a permutation of the 5 roots) — a canonical, tunable-free
arithmetic symbol. We built the Frobenius symbol sequence for quintics of three Galois types and
ran the Phase-4 saturation harness (does a windowed phase-depth statistic deviate from a `k`-th
order Markov null?), with a train/test split for honest significance.

Quintics (Galois group verified by Frobenius-density signature):
`C₅` = `x⁵+x⁴−4x³−3x²+3x+1` (= ℚ(ζ₁₁)⁺; Frobenius ≈ `p mod 11`) ·
`D₅` = `x⁵−x⁴−5x³+4x²+3x−1` (the pentagon's own group) · `S₅` = `x⁵−x−1`.

## Result (10⁷ primes for D₅/S₅; 5×10⁷ for the abelian baselines)

| system | #windows | k=1 (pairwise) | k=2 | k=3 |
|---|---|---|---|---|
| residue mod 5 | 600,226 | TV .0217, **p 10⁻¹²⁶** | TV .0120, p 10⁻⁶³ | TV .0127, p 10⁻⁶¹ |
| C₅ (`p mod 11`) | 600,226 | TV .0136, **p 10⁻¹¹¹** | TV .0109, p 10⁻⁶⁷ | TV .0104, p 10⁻⁷¹ |
| **D₅** | 132,914 | TV .0046, **p 9.5×10⁻³** | TV .0044, p 3.6×10⁻² | TV .0045, p 3.5×10⁻² |
| **S₅** | 132,914 | TV .0020, **p 0.31** | TV .0022, p 0.36 | TV .0025, p 0.34 |

## Verdict — the escape fails, and it fails *informatively*
1. **Abelian arithmetic data is strongly, low-order correlated.** Residues mod 5 and the abelian-
   Galois Frobenius `p mod 11` both show enormous consecutive-correlation signal (`p` ≈ 10⁻⁶⁰…10⁻¹²⁶)
   — the Lemke Oliver–Soundararajan bias. This is exactly the regime standard Fourier/Dirichlet
   analysis already sees.
2. **Non-abelian Galois (Frobenius) data is *near-independent*.** `S₅` is statistically null
   (`p` ≈ 0.3 — consistent with an i.i.d. Frobenius sequence); `D₅` is only marginal
   (`p` ≈ 0.01–0.04, TV ≈ 0.004). Consecutive non-abelian Frobenii carry **far less** correlation
   than abelian residues — Chebotarev independence is cleaner in the non-abelian case.
3. **So the naive escape is refuted, in the opposite direction from the hope.** Making the fiber
   nonabelian and the input multiplicative does *not* buy higher-order structure; it buys *less*,
   because the non-abelian arithmetic input is closer to noise. The phase-depth windowed holonomy's
   reach is bounded by the low-order correlation of its input, and the richest such correlation lives
   in **abelian** (Fourier-accessible) data — precisely what standard analysis already exhausts.

## The reframing this forces (where the real arithmetic is)
The windowed-holonomy experiments (Phase 4 + D) probe **consecutive-prime correlations**. But the
genuine arithmetic content of the Frobenius cocycle — the plan's crown — is **not** a consecutive-
correlation statistic at all. It is the *structural* identity

> holonomy = Artin symbol ⟹ the transfer-operator dynamical zeta **is** the Artin L-function,

which is a sum over **all** primes of `χ(Frob_p)`, a *global* object, blind to whether neighbouring
Frobenii correlate. The empirical no-go says: **stop looking for the signal in consecutive-prime
statistics — there is none beyond the abelian L-O-S regime.** The arithmetic lives in the global
spectral identity, which is *formal, not statistical*, and therefore something to **prove**
(Movement A/B give the zeta and trace formula; the remaining step is the Frobenius-cocycle ⟹
Artin-L identity), not to measure.

## Honest scope
- The cycle-type symbol coarsens the true Frobenius (e.g. D₅'s two 5-cycle classes `{r,r⁴}`,
  `{r²,r³}` merge into one symbol), and the "repeat count" is one coarse statistic; a finer
  observable could differ. The train/test split carries a mild non-stationarity artifact (prime
  statistics drift with size), which inflates the abelian residuals at k≥2 but cannot manufacture
  the abelian-vs-nonabelian gap of ~60 orders of magnitude in `p`.
- This bounds *these* constructions/statistics empirically; it is not a proof. The decisive next
  step is the **structural** Artin-L identity, not another statistic.
