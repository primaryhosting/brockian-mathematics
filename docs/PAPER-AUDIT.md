# Paper Audit — 7 Brockian papers vs. the verified core (2026-08-01)

Two independent review passes mapped every substantive claim in seven Brockian papers to
`registry/theorems.json` (the machine-verified core) and the intake ledger's named failure
modes. **Register caveat:** registry proofs are AXLE-attested @ lean-4.32.0 but flagged
`quarantine: true` / `lake_build: pending` — "VERIFIED" here means "matches a machine-attested
registry theorem," not "independently rebuilt / published."

## What is genuinely real across all 7 papers — exactly two cores

1. **The q−2 / q−ν admissibility law** — `Brockian.Admissibility.universal_admissibility_count`
   (+ `admissibility_count_three/five`), refined to the general `q − ν` (image-count) law.
   PROVED, citation-grade.
2. **Classical pentagon/golden facts** — `cos(2π/5)=(φ−1)/2`, `φ−1 ∈ spec(C₅)`,
   `golden_unique_to_five`, `λ₂(C₅)=2−1/φ`, `Aut(C₅)≅D₅`, `5∣fib n ⟺ 5∣n`. All PROVED.

Everything else is (i) the unproven **equidistribution conjecture** dressed as a proven "Law",
(ii) an **automorphism-group conflation**, or (iii) a **wrong-object eigenvalue** claim.

## Per-paper verdict

| Paper | Verified core | Verdict |
|-------|---------------|---------|
| `Universal_Formula_Paper` ("q−2 Theorem") | Thm 1.1 = `universal_admissibility_count` | **Most rigorous.** Equidistribution honestly flagged conjectural. §6.5 k-tuple `(q−1)^{k−1}` guess **superseded** by the verified q−ν law. |
| `Rigorous_Mathematical_Paper` (prime pairs mod 5) | Thm 3.1 = `admissibility_count_five` | **Restrained, headline verified.** Minor: Def 2.4 smuggles an unproven positive-density clause into "principal". |
| `Finite-Range_Deviation_Study` | uses q=5→3 | **Honest methodology/empirical.** Nothing to retract; treats 1/3 as a *hypothesis to test*. |
| `Geometric_Arithmetic_Foundations` | cos identity, `fib_five_dvd`, p−2 count, (restated) `Aut(C₅)≅D₅` | **Two headline theorems defective as stated**: Thm 3.5 conflates automorphism groups; Thm 4.3 attaches φ to the rotation *matrix* spectrum (eigenvalues e^{±2πi/5}, complex — false); real fact is φ−1 ∈ *adjacency* spectrum. |
| `Brockian_Universal_Law_Whitepaper` | Thm 3.1(I) count, cos identity | **Central overclaim**: promotes unproven equidistribution to "the Universal Pentagonal Law … exact, not probabilistic, verified" while listing it as Open Problem 1; ships `principal_pair_count := by sorry`; "None represent unproven conjectures" is self-contradictory. |
| `Paper_BV_Final` | q−ν count + singular-series positivity | **Headline (Thm 1.2/Lemma 3.2 "rigorous BV equidistribution") is a SKETCH.** BV quoted genuinely (real `x^{1/2}`, not the run-62 ℕ-collapse) but only as a cited classical theorem; Brock's application is unproven and absent from the registry. |
| `GeometricArithmetic_MagnumOpus` | one trivial theorem (Thm 2.4) | **~90% book shell**: Ch 3–11 + all appendices (incl. "Complete Lean 4 Formalization", crypto applications) are EMPTY title pages; abstract's "600+ lines verified Lean / applications demonstrated" is unsupported by the document. |

## Retraction / downgrade flags (both audits agree)

- **`Brockian_Universal_Law_Whitepaper`** — retract "exact/verified Law" framing of equidistribution; it is Open Problem 1 (BV/HL-strength). The ledger's "complete transition support" rename exists precisely to stop this conflation.
- **`Paper_BV_Final`** — downgrade Thm 1.2 / Lemma 3.2 / abstract from "rigorous theorem" to heuristic/attackable-target.
- **`Geometric_Arithmetic_Foundations`** — fix Thm 3.5 (automorphism conflation) and Thm 4.3 (rotation-matrix eigenvalue is not φ).
- **`GeometricArithmetic_MagnumOpus`** — abstract claims exceed delivered content; either complete the chapters or reframe as a prospectus.

## Ranked new attackable targets these papers surface (not already in the registry)

| # | Target | Yield / cost | Status |
|---|--------|--------------|--------|
| 1 | **Conditional equidistribution schema** (HL/BV ⇒ density 1/(q−ν)) — legitimizes the central overclaim as an honest rung-3 conditional | highest / medium | **launched** (`EquidistributionSchema`) |
| 2 | **Affine group Aff(1,F_q) as the true symmetry** — fixes the recurring automorphism error into a correct theorem | high / medium | **launched** (`AffineSymmetry`) |
| 3 | **CRT composite-modulus count** — corrects `Paper_BV_Final §6.1`'s suspect factor | high / low | **launched** (`AdmissibilityCRT`) |
| 4 | **Divisible-case diagonal law** (g≡0 mod q → q−1 configs) — completes the dichotomy | medium / low | queued |
| 5 | **Exact k-tuple configuration count** (general admissible tuple, CRT + inclusion–exclusion) — replaces the superseded `(q−1)^{k−1}` guess | high / medium | queued |
| 6 | **Galois/algebraic-degree classification of C_p spectra** — generalizes `golden_unique_to_five` | medium / hard | queued |

**Through-line:** the papers are strongest exactly where they match the registry and overclaim
exactly where they leave it. The verified core is the arbiter — targets 1–3 turn the biggest
overclaims/errors into legitimate theorems.
