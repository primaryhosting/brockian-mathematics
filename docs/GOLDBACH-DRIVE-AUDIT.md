# Goldbach prior-work audit — Drive corpus vs. the verified core (2026-08-02)

Audit of the prior Goldbach work in Google Drive + local Downloads against the verified registry,
in the intake-ledger tradition: what is **backed**, what is **new-and-formalizable**, what is
**empirical/conditional** (not provable-as-stated), and what has been **retired as overclaim**.

## Method

The Drive Goldbach corpus consolidates into two review-hardened July-2026 papers (each superseding
June drafts + the local PDFs). Both were read in full; claims mapped to `registry/theorems.json`
(the core already carries ~150 PROVED Goldbach-adjacent theorems: `GoldbachComb`, `GoldbachParity`,
`GoldbachLemmas`, `GoldbachSchema`, `Goldbach.LocalWheel`, `Goldbach.WheelExtended`,
`Goldbach.WheelK2357`, `Goldbach.CovarianceScaffold`, plus `Admissibility*`, `AffineSymmetry`,
`EquidistributionUniformity`). The older Drive `*-output.lean` and `GoldbachComb.lean` files are
prior Aristotle drafts, superseded by the fresh AXLE-verified core.

## Per-source verdict

| Source | Nature | Verdict |
|--------|--------|---------|
| `paper1_affine` (Affine Selection Rules for Goldbach and Prime Gaps, Jul 2026) | elementary, finite ℤ/ℓ | **HARVEST — in progress** (`GoldbachSelectionRule.lean`) |
| `paper2_tomography` (Goldbach Tomography — three instruments, Jul 2026) | computational + RH-conditional | **No new unconditional target**; honest conditional/conjecture scaffolds only |
| local PDFs (Comet Anatomy, Hearing the Zeros, Robustness Tests) | empirical | Consolidated into `paper2_tomography`; empirical, not formalizable-as-proved |
| Drive `GoldbachComb.lean`, `AffineSelection.lean`, `*-output.lean` | prior Lean drafts | Superseded by the AXLE-verified core |
| `Collected_Work_2.pdf`, `vol2.pdf` | broad corpus aggregations | Out of Goldbach scope here; broader-corpus sweep TBD |

## paper1_affine — the one genuinely-new formalizable target (being harvested)

Unconditional, finite, honesty-first. The core has the *pieces* (affine group `dihedralToPerm`,
gap-side `admissibility_count_dichotomy`, `goldbachCount_four`, reflection lemmas) but **not the
unified statement**:

- **AS-1 (general affine selection rule):** for odd prime ℓ and `f(x)=εx+a`, `|A_ℓ(f)| = ℓ−1` if
  `f(0)=0` else `ℓ−2`. Proof: `f` bijective ⇒ `f(x)=0` has one solution `x₀=f⁻¹(0)`; the admissible
  set excludes `x=0` (domain) and `x=x₀` (codomain), coinciding iff `f(0)=0`.
- **AS-2/AS-3:** gap law = translation restriction (`f(x)=x+g`); Goldbach law = reflection
  restriction (`f(x)=c−x`).
- **AS-5 (dihedral envelope):** `Σ_m = {x↦x+a} ∪ {x↦a−x} ≅ D_m` (order 2m), gaps = rotations,
  Goldbach = reflections.
- **Pentagonal case (ℓ=5):** `|𝒢(c)| = 4 if c=0 else 3`; `|𝒯(g)| = 4 if 5|g else 3` — the 4/3 local
  factor `(5−1)/(5−2)`, the **Goldbach↔pentagon bridge**.

Status: launched as `Brockian/GoldbachSelectionRule.lean` (board claim 2026-08-02). Corrects the
predecessor's unsafe "5 is the smallest prime with nontrivial affine structure" (it is not — D₃
exists; 5 is smallest with *four* active nonzero classes) — the corrected framing is what we formalize.

## paper2_tomography — empirical/conditional; no new unconditional proof target

Three *distinct* projections (kept apart under one-name-one-object discipline), not terms of one
identity — the earlier additive "three-term decomposition" is **explicitly retired**:

- **Instrument I (pointwise):** the singular-series kernel `s(n)=∏_{p|n,p>2}(p−1)/(p−2)` explains
  ~99.99% of `log R` variance; Euler factors reconstructed from data. The *math* (singular series +
  local factors) is **already PROVED-and-in-core** (`SingularSeries*`, `Admissibility*`); the paper's
  content here is empirical verification, not a new theorem.
- **Instrument II (summatory, Λ-weighted):** Fujii's explicit formula (∑G(n) as zeta-zero modes) —
  **RH-conditional, and an external classical theorem** (Fujii 1991). Formalizable only as a
  named-hypothesis CONDITIONAL scaffold; low marginal value (it is cited, not ours). Would slot beside
  `RiemannScaffold` if wanted.
- **Instrument III (residual covariance):** the sign law `ACF(k)>0 ⟺ 3|k` and the covariance-kernel
  = singular-series connection are recorded by the paper itself as a **CONJECTURE** (one dataset,
  fitted constants α≈0.030, c≈0.036). NOT provable-as-stated; honest register = CONJECTURE/COMPUTATION.

**Honesty carried over:** the paper withdraws "the last 0.01% is the zeta zeros," demotes per-zero
significance counts, and reserves the word "exact" for the census (FFT roundoff ≠ representability).
Nothing here is claimed to bear on RH.

## Recommendation

1. **Finish the affine-selection harvest** (in flight) — the sole new unconditional target; it unifies
   the gap + Goldbach + pentagon lanes and bridges to the 4/3 local factor. AXLE-gate as usual.
2. **Do NOT** attempt to formalize the tomography instruments as proved — they are empirical /
   RH-conditional / conjectural by the author's own careful framing. If desired, record two HONEST
   ledger items, clearly marked and never counted as PROVED:
   - a CONDITIONAL scaffold for Fujii's explicit formula (named RH hypothesis), and
   - a CONJECTURE for the covariance kernel (`ACF(k)>0 ⟺ 3|k`).
3. The broad corpus (`Collected_Work_2`, `vol2`) is a separate, non-Goldbach sweep if wanted —
   likely already reflected in the core + the earlier 98-source ingest.

**Bottom line:** the prior Goldbach work was worth harvesting — for exactly one thing (the affine
selection rule), which is being formalized now; the rest is honest empirical/conditional material that
the core already covers or that must stay unproved. No overclaim survives the mapping.
