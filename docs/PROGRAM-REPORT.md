# Brockian Verified Core — Program Report

**Audience:** technical partners, advisors, scientific collaborators
**Classification:** Partner-facing (non-confidential). Counts pinned to the live registry.
**Report generated:** 2026-08-03
**Tip commit:** `296dfb95b34487dc78e6c5111871b3823af2dce7` (`296dfb9`) — *feat(number-theory): prove Wolstenholme theorem* (2026-08-03 12:22:30 -0400)
**Registry source:** `registry/theorems.json`
**Generated from:** AXLE attestations

> **Brand sentence:** *We ship what is proven and mark what is not.*

Regenerate this document anytime:

```bash
python3 scripts/gen_program_report.py
```

Partner strategy context (do not confuse with this ledger snapshot):
[`docs/partner/2026-08-02-verified-intelligence-strategy-brief.md`](partner/2026-08-02-verified-intelligence-strategy-brief.md)

---

## 1. Executive summary

The **Brockian Verified Core** is a Lean 4 + Mathlib formalization program with a
hard honesty firewall: a declaration is **PROVED** only when it is sorry-free,
uses only standard axioms, and carries an independent **AXLE** verification
verdict at a pinned environment. Registers are **derived** by
`scripts/gen_registry.py` — never hand-painted.

| Snapshot | Value |
|----------|------:|
| **PROVED** | **10568** |
| **DEFINITION** | **581** |
| **CONDITIONAL** | **20** |
| **DISCHARGED** | **7** |
| **CONJECTURE** | **40** |
| Declarations in registry | 11216 |
| Modules with entries | 745 |
| Module attestation files | 746 |
| Certificate factory units | 3 (`CosTraceNorm`, `FranklinFixedPoint`, `target`) |
| AXLE environment | `lean-4.32.0` |
| AXLE verdict = verified | 11216 / 11216 |
| Local `lake_build` field | **11216 pending** (see §6 caveats) |

**What closed (reference process wins):** Euler’s pentagonal number theorem
unconditionally in-core; Galois / “why five” degree rigidity; the q−ν
admissibility law; D₅ / C₅ spectral structure; large local Goldbach and
singular-series kernels; and bounded Kato-Rellich for unbounded ESA cores.

**What stays open (explicit non-claims):** Riemann Hypothesis, global Goldbach
transfer, the normalized Schwartz/Fourier intertwining, oscillator ESA, and the
concrete weighted Rellich compact embedding — scaffolded or conditional,
**not** counted as PROVED.

---

## 2. Register table (source of truth)

Registers are derived from axioms + AXLE verdict + provenance rung
(DISCHARGED = former CONDITIONAL whose hypothesis was later proved in-core).

| Register | Count |
|----------|------:|
| **PROVED** | 10568 |
| **DEFINITION** | 581 |
| **CONDITIONAL** | 20 |
| **DISCHARGED** | 7 |
| **CONJECTURE** | 40 |

| Meaning | Gate |
|---------|------|
| **PROVED** | Sorry-free; axioms ⊆ `{propext, Classical.choice, Quot.sound}`; no `native_decide`; **AXLE verified** at named env |
| **DEFINITION** | Supporting `def` / structure (not a theorem claim) |
| **CONDITIONAL** | Depends on a named hypothesis (`conditional_rung` set) |
| **DISCHARGED** | Former CONDITIONAL closed by a later in-core PROVED result |
| **CONJECTURE** | Named Prop container — never typed as an unconditional theorem |

Full enumeration: [`REGISTRY.md`](../REGISTRY.md) · machine JSON: [`registry/theorems.json`](../registry/theorems.json).

### Theme distribution (module-name clustering; not a second ledger)

| Theme cluster | Entries |
|---------------|--------:|
| Goldbach / singular series | 7609 |
| Galois / cyclotomic / cos-trace | 1381 |
| Weyl / spectral / operator | 706 |
| Other | 618 |
| D₅ / C₅ spectral & symmetry | 389 |
| Pentagonal / Franklin / partition | 151 |
| Admissibility / sieve | 124 |
| Core / metallic / golden | 78 |
| Equidistribution | 64 |
| Penrose | 64 |
| Riemann / ξ scaffold | 32 |

---

## 3. Flagship results (registry-backed samples)

Only names that exist in the current registry are listed. Partners should click
through to the declaration, not treat the blurb as a substitute proof.

- **Euler pentagonal number theorem (unconditional close).** Franklin fixed-point path; prior conditional forms reclassified DISCHARGED.
  - `Brockian.FranklinFixedPoint.pentagonalNumberTheorem` **[PROVED]**
- **Why five / golden rigidity.** Quadratic degree for cos-generator iff p = 5; degree formulas for 3/5/7.
  - `Brockian.GaloisWhyFive.why_five` **[PROVED]**
  - `Brockian.GaloisWhyFive.quadratic_iff_five` **[PROVED]**
  - `Brockian.GaloisWhyFive.degree_five` **[PROVED]**
- **Admissibility q−ν law.** Exact start-residue counts mod q; twin (mod 3) and Brockian (mod 5) cases.
  - `Brockian.Admissibility.universal_admissibility_count` **[PROVED]**
  - `Brockian.Admissibility.admissibility_count_five` **[PROVED]**
  - `Brockian.Admissibility.admissibility_count_three` **[PROVED]**
- **Aut(C₅) ≅ D₅.** Faithful dihedral action upgraded to full automorphism isomorphism.
  - `Brockian.Automorphism.Full.aut_equiv_dihedral` **[PROVED]**
  - `Brockian.Automorphism.Full.aut_card_eq_ten` **[PROVED]**
- **Algebraic connectivity / golden spectrum on C₅.** Laplacian gap and golden eigenvalue membership unique at five.
  - `Brockian.Connectivity.pentagon_lambda2_phi` **[PROVED]**
  - `Brockian.ConnectivityGoldenBridge.algebraic_connectivity_C5` **[PROVED]**
  - `Brockian.C5SpectralMultiplicities.golden_unique_to_five_setlevel` **[PROVED]**
- **ξ functional equation & zero reflection (scaffold).** Scaffolding for Hilbert–Pólya-style attack; RH itself remains CONDITIONAL/open.
  - `Brockian.XiFunctionalEquation.riemannXi_functional_equation` **[PROVED]**
  - `Brockian.RiemannXiSymmetry.riemannXi_eq_zero_iff_reflect` **[PROVED]**
  - `Brockian.RiemannScaffold.riemannXi_eq_zero_of_nontrivial_zeta_zero` **[PROVED]**
- **Local Goldbach / singular series kernel.** Local kernels proved; global Goldbach transfer is CONJECTURE, not PROVED.
  - `Brockian.Goldbach.CovarianceScaffold.singular_series_finite_goldbachPairTuple_pos_of_even` **[PROVED]**
  - `Brockian.SingularSeries.localFactorAt_eq` **[PROVED]**

### Certificate factory (unit of progress)

Recent program direction: certificates as first-class artifacts under
`registry/certificates/`. Present units: `CosTraceNorm`, `FranklinFixedPoint`, `target`.

---

## 4. Explicit NON-CLAIMS

Marketing and partner decks **must not** promote the following as unconditional
closes. Status is taken from the registry when the name is present.

| Topic | Registry name | Register | Note |
|-------|---------------|----------|------|
| **Riemann Hypothesis** | `Brockian.RiemannScaffold.RH_of_BrockianSystem` | **CONDITIONAL** | Scaffolded as CONDITIONAL on a named BrockianSystem hypothesis; not shut. |
| **Global Goldbach transfer** | `Brockian.GoldbachComb.GoldbachCovarianceTransfer` | **CONJECTURE** | Named CONJECTURE (Prop container); local covariance is PROVED separately. |
| **Historical Kato transfer rung** | `Brockian.Weyl.KatoUnbounded.essentiallySelfAdjoint_perturb` | **DISCHARGED** | DISCHARGED by the unconditional graph-closure theorem in WeylKatoRellich. |
| **Free Laplacian ESA via Plancherel (full link)** | `Brockian.FreeLaplacianPlancherel.freeLaplacian_essentiallySelfAdjoint_via_plancherel` | **CONDITIONAL** | Plancherel infrastructure partially closed; full free −Δ ESA via Fourier still CONDITIONAL. |
| **Global equidistribution / BV transfer** | `Brockian.EquidistributionBVReduction.configCount_density_of_BV` | **CONDITIONAL** | Reduction lemmas present; density/BV uniformity steps stay CONDITIONAL. |

### All CONDITIONAL entries (20)

| Name | Module |
|------|--------|
| `Brockian.Equidistribution.equidistribution_of_asymptotic` | `Brockian.Equidistribution` |
| `Brockian.Equidistribution.equidistribution_of_asymptotic_exists` | `Brockian.Equidistribution` |
| `Brockian.EquidistributionBVReduction.configCount_density_of_BV` | `Brockian.EquidistributionBVReduction` |
| `Brockian.EquidistributionBVReduction.configCount_over_main_tendsto` | `Brockian.EquidistributionBVReduction` |
| `Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform` | `Brockian.EquidistributionBVReduction` |
| `Brockian.EquidistributionBVReduction.total_over_main_tendsto` | `Brockian.EquidistributionBVReduction` |
| `Brockian.EquidistributionUniformity.equidistribution_of_transitive_symmetry` | `Brockian.EquidistributionUniformity` |
| `Brockian.EquidistributionUniformity.sing_uniform_of_transitive` | `Brockian.EquidistributionUniformity` |
| `Brockian.FreeLaplacianPlancherel.freeLaplacian_essentiallySelfAdjoint_via_plancherel` | `Brockian.FreeLaplacianPlancherel` |
| `Brockian.GoldbachSchema.goldbach_beyond_of_model` | `Brockian.GoldbachSchema` |
| `Brockian.GoldbachSchema.goldbach_from_spectral_model` | `Brockian.GoldbachSchema` |
| `Brockian.RiemannScaffold.RH_of_BrockianSystem` | `Brockian.RiemannScaffold` |
| `Brockian.Weyl.DeficiencyODE.deficiencyRepresentsODE_of_weakRegularity` | `Brockian.Weyl.DeficiencyODE` |
| `Brockian.Weyl.DeficiencyODE.schrodinger_essentiallySelfAdjoint_of_weakRegularity` | `Brockian.Weyl.DeficiencyODE` |
| `Brockian.Weyl.FreeLaplacian2.freeLaplacian_essentiallySelfAdjoint_of_fourier` | `Brockian.Weyl.FreeLaplacian2` |
| `Brockian.Weyl.SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode` | `Brockian.Weyl.SchrodingerMinimal` |
| `Brockian.Weyl.WeylLawTarget.counting_diverges_of_candidate` | `Brockian.Weyl.WeylLawTarget` |
| `Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_WeylLawMatch` | `Brockian.Weyl.WeylLawTarget` |
| `Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_rvm` | `Brockian.Weyl.WeylLawTarget` |
| `Brockian.Weyl.WeylLawTarget.counting_diverges_of_exists` | `Brockian.Weyl.WeylLawTarget` |

### All DISCHARGED entries (7)

| Name | Module |
|------|--------|
| `Brockian.FranklinInvolution.franklin_of_franklinData` | `Brockian.FranklinInvolution` |
| `Brockian.FranklinInvolution.pentagonalNumberTheorem_of_franklinData` | `Brockian.FranklinInvolution` |
| `Brockian.FranklinInvolution.signedSum_eq_pentCoeff_of_franklinData` | `Brockian.FranklinInvolution` |
| `Brockian.FranklinInvolutionProof.pentagonalNumberTheorem_of_franklinMap` | `Brockian.FranklinInvolutionProof` |
| `Brockian.PentagonalTheoremFranklin.pentagonalNumberTheorem_of_franklin` | `Brockian.PentagonalTheoremFranklin` |
| `Brockian.PentagonalTheoremFranklin.pentagonalProduct_coeff_of_franklin` | `Brockian.PentagonalTheoremFranklin` |
| `Brockian.Weyl.KatoUnbounded.essentiallySelfAdjoint_perturb` | `Brockian.Weyl.KatoUnbounded` |

### All CONJECTURE entries (40)

| Name | Module |
|------|--------|
| `Brockian.AmicableNumbers.AmicableInfinitude` | `Brockian.AmicableNumbers` |
| `Brockian.AndricaConjecture.AndricaConjecture` | `Brockian.AndricaConjecture` |
| `Brockian.BetrothedNumbers.BetrothedInfinitude` | `Brockian.BetrothedNumbers` |
| `Brockian.BetrothedNumbers.SameParityBetrothedExists` | `Brockian.BetrothedNumbers` |
| `Brockian.BrocardGap.BrocardGapConjecture` | `Brockian.BrocardGap` |
| `Brockian.BrocardProblem.BrocardConjecture` | `Brockian.BrocardProblem` |
| `Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude` | `Brockian.CarmichaelKorselt` |
| `Brockian.CollatzPartial.CollatzConjecture` | `Brockian.CollatzPartial` |
| `Brockian.CullenWoodall.CullenPrimeInfinitude` | `Brockian.CullenWoodall` |
| `Brockian.CullenWoodall.WoodallPrimeInfinitude` | `Brockian.CullenWoodall` |
| `Brockian.ErdosStraus.ErdosStrausConjecture` | `Brockian.ErdosStraus` |
| `Brockian.FermatNumbers.FermatPrimeBeyondFour` | `Brockian.FermatNumbers` |
| `Brockian.FortunateNumbers.FortuneConjecture` | `Brockian.FortunateNumbers` |
| `Brockian.GilbreathConjecture.GilbreathConjecture` | `Brockian.GilbreathConjecture` |
| `Brockian.GiugaNumbers.OddGiugaExists` | `Brockian.GiugaNumbers` |
| `Brockian.GoldbachComb.GoldbachCovarianceTransfer` | `Brockian.GoldbachComb` |
| `Brockian.HyperperfectNumbers.HyperperfectAllK` | `Brockian.HyperperfectNumbers` |
| `Brockian.HyperperfectNumbers.HyperperfectInfinitude` | `Brockian.HyperperfectNumbers` |
| `Brockian.LandauNSquaredPlusOne.LandauFourthConjecture` | `Brockian.LandauNSquaredPlusOne` |
| `Brockian.LegendreConjecture.LegendreConjecture` | `Brockian.LegendreConjecture` |
| `Brockian.MersennePerfect.EvenPerfectInfinitude` | `Brockian.MersennePerfect` |
| `Brockian.MersennePerfect.MersennePrimeInfinitude` | `Brockian.MersennePerfect` |
| `Brockian.OppermannConjecture.OppermannConjecture` | `Brockian.OppermannConjecture` |
| `Brockian.OreHarmonicNumbers.OddHarmonicExists` | `Brockian.OreHarmonicNumbers` |
| `Brockian.PalindromicPrimes.PalindromicPrimeInfinitude` | `Brockian.PalindromicPrimes` |
| `Brockian.PerfectTotient.PerfectTotientInfinitude` | `Brockian.PerfectTotient` |
| `Brockian.PolignacPrimes.PolignacConjecture` | `Brockian.PolignacPrimes` |
| `Brockian.PracticalNumbers.PracticalTwinInfinitude` | `Brockian.PracticalNumbers` |
| `Brockian.QuasiperfectNumbers.QuasiperfectExists` | `Brockian.QuasiperfectNumbers` |
| `Brockian.RepunitPrimes.RepunitPrimeInfinitude` | `Brockian.RepunitPrimes` |
| `Brockian.RieselCovering.RieselProblem` | `Brockian.RieselCovering` |
| `Brockian.RuthAaronPairs.RuthAaronInfinitude` | `Brockian.RuthAaronPairs` |
| `Brockian.SierpinskiCovering.SierpinskiProblem` | `Brockian.SierpinskiCovering` |
| `Brockian.SophieGermain.SophieGermainInfinitude` | `Brockian.SophieGermain` |
| `Brockian.SuperperfectNumbers.OddSuperperfectExists` | `Brockian.SuperperfectNumbers` |
| `Brockian.TwinPrimes.TwinPrimeConjecture` | `Brockian.TwinPrimes` |
| `Brockian.UnitaryPerfect.SixthUnitaryPerfectExists` | `Brockian.UnitaryPerfect` |
| `Brockian.WeirdNumbers.OddWeirdExists` | `Brockian.WeirdNumbers` |
| `Brockian.WilsonPrimes.WilsonPrimeInfinitude` | `Brockian.WilsonPrimes` |
| `Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure` | `Brockian.ZumkellerNumbers` |

---

## 5. Multi-prover operations

Heterogeneous engines write candidates; **one registry** decides the badge.

| Role | Engine | What it is trusted for |
|------|--------|-------------------------|
| **Independent verify** | **AXLE** (Axiom Lean Engine) | Statement + proof re-check at pinned `lean-4.32.0`; required for PROVED |
| **Hard classical generation** | **Aristotle** (Harmonic) | Proof generation / port for difficult targets; **never** a substitute for AXLE |
| **Frontier reduce / modules** | Codex / Grok (parallel tools) | Schema reduction, scaffolding, large module drafts; gated before tip merge |
| **Orchestration + hygiene** | Local scripts + human tip | `gen_registry`, no-theater lint, dependency firewall, settle/certificates |

**Triple verification ideal for PROVED:**

1. Local `lake build` on pinned toolchain
2. Local `#print axioms` ⊆ standard three
3. AXLE `verified` at named environment

**Today’s registry field reality:** AXLE + axiom gate are populated for all
listed entries; the `lake_build` stamp is still largely `pending` (see below).
That is an operational caveat, not a license to inflate PROVED.

---

## 6. Caveats partners must know

### 6.1 AXLE vs local lake

| Leg | Status in this export |
|-----|------------------------|
| AXLE independent check | **11216/11216** verdict `verified` @ `lean-4.32.0` |
| Axioms clean flag | **11216/11216** `axioms_ok: true` |
| Local `lake_build` stamp | **11216/11216** marked `pending` |

**Implication:** Partner-grade “verification company” narrative requires a
reproducible local/CI `lake build` leg alongside AXLE. Treat current PROVED as
**AXLE-attested + axiom-gated**, with local lake stamp not yet written into
every registry row. Third parties should still run:

```bash
lake exe cache get
lake build
```

on the tip commit above.

### 6.2 Counting discipline

- **Registry PROVED** (10568) is the only number safe for partner headlines.
- Campaign / historical “theorems attempted” totals are **not** interchangeable with PROVED.
- DEFINITION (581) supports the API surface; do not add it to PROVED.
- DISCHARGED (7) is a success story (conditionals closed) — **not** extra PROVED.

### 6.3 No theater

Excluded failure modes (definitional theater, ℝ-mod collapse, smuggled
`native_decide`, overtitling, etc.) are documented in process notes; they are
not silently upgraded. See honesty commitments in the repo root `README.md` and
[`docs/NEW-ERA.md`](NEW-ERA.md).

---

## 7. Strategic reading (for partners)

The pentagonal / Brockian math program is the **crucible**. The **product** is
verification-gated reasoning: formalize → multi-prover verify → deploy only what
the ledger proves.

| Deploy vector | Role of this program |
|---------------|----------------------|
| **QuantumProof / IonQ** | Formal security/entropy/PQC properties with registry badges |
| **SAIR / distillation** | Train and score on machine-checked traces, not unverified CoT |
| **Public registry surface** | Observatory / torus must pull badges from this SSOT |

Full partner strategy brief (tone, 90-day plan, risk table):

→ **[`docs/partner/2026-08-02-verified-intelligence-strategy-brief.md`](partner/2026-08-02-verified-intelligence-strategy-brief.md)**

---

## 8. How to re-verify this report

```bash
# 1. Pin the tip
git rev-parse HEAD

# 2. Recompute counts (must match §2)
python3 -c "import json; d=json.load(open('registry/theorems.json')); print(d['summary'])"

# 3. Regenerate this document
python3 scripts/gen_program_report.py

# 4. Optional: full registry + paper tables from attestations
python3 scripts/gen_registry.py
python3 scripts/gen_paper_theorem_table.py
```

**Pin phrase for external one-pagers:**

> As of commit `296dfb9` (2026-08-03): **10568 PROVED**, **581 DEFINITION**, **20 CONDITIONAL**, **7 DISCHARGED**, **40 CONJECTURE** — from `registry/theorems.json`.

---

*This file is generated. Edit `scripts/gen_program_report.py` for structure; never hand-edit counts.*
