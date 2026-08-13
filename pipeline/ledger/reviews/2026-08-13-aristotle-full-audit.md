# Aristotle two-account proof audit — 2026-08-13

**Status:** evidence audit and editorial triage; **not** a mathematical-novelty certification.

## Pinned inputs

- Repository: [primaryhosting/brockian-mathematics](https://github.com/primaryhosting/brockian-mathematics)
- Main snapshot: `990b7af54325994760f2794dd728368ad79197ce`
- Quantum release: [PR #1](https://github.com/primaryhosting/brockian-mathematics/pull/1), head `29f1faa35306dc27290c14b26704d5ae6e0eb4c1`
- Cross-domain release: [PR #2](https://github.com/primaryhosting/brockian-mathematics/pull/2), head `5c87f4df6f6d26b0aa4c9467fab72e8310684ac7`
- Audit/novelty ledger: [PR #3](https://github.com/primaryhosting/brockian-mathematics/pull/3)
- Latest completion-email snapshot reviewed: 307 completion messages, 286 unique Aristotle UUIDs, and 159 named targets. The connected mailbox exposes watcher copies identifying both `admin` and `chris`; it does not expose the `admin@primary.hosting` inbox directly.
- The GitHub harvest ledger is broader and is the canonical two-account snapshot for this audit.

## What each gate means

1. **Aristotle `PROVED`** means the remote job reported completion. It is not a Lean compilation certificate.
2. **Selected** means `best_proofs/manifest.json` chose one source for a target.
3. **AXLE pass** means the normalized source has `verified: true` in `aristotle/axle_verify.json` for Lean 4.32.0/Mathlib.
4. **Static source scan** found no local `axiom` declarations and no `sorry`/`admit` proof placeholders in the 717 passing sources. This does not enumerate axioms inherited from imports.
5. Only 52 of 717 passing files contain a `#print axioms` directive. A complete saved per-theorem axiom report is still required before the stronger phrase “axiom-clean” is used corpus-wide.
6. **Classification** below is human editorial triage based on exact statements, hypotheses, proof shape, and reuse potential. It is not formal metadata and does not establish novelty.

## Verification funnel

| Gate | Count | Interpretation |
| --- | ---: | --- |
| Aristotle jobs | 1638 | 1522 `PROVED`; 116 `STOPPED` |
| Jobs by account | 683 admin / 955 chris | Both account streams are present in the harvested ledger |
| Distinct targets in ledger | 982 | Includes stopped-only targets |
| Distinct targets with ≥1 `PROVED` job | 918 | Remote completion only |
| Selected targets | 916 | Two proved targets are unselected |
| AXLE passing selected targets | 717 | Compile gate passed |
| AXLE failing selected target entries | 197 | Do not release as verified |
| Indeterminate AXLE entries | 2 | `problem_normal_0001`; `Brockian.LegendreConjecture.LegendreConjecture` |
| Open-PR release candidates | 181 | 34 in PR #1; 147 in PR #2 |
| Passing files with `#print axioms` | 52 | Full corpus axiom reporting remains incomplete |

The proved targets without a selected source are `Frontier.avila_ten_martini` and `Frontier.furstenberg_szemeredi`.

The sanitizer also has one collision: `D5_card` and `D5.card` both map to `D5_card.lean`. Both target entries therefore inherit the same currently failing AXLE record; selection must move to collision-resistant paths.

## Classification

| Class | Count | Working definition |
| --- | ---: | --- |
| Routine formalization | 561 | Direct standard fact, definitional/reflexive theorem, closed finite calculation, repeated parameter instance, or a conditional/equivalent-premise scaffold |
| Useful library result | 153 | Reusable nontrivial lemma/API or known theorem development with plausible downstream or upstream value |
| Potentially research-significant | 3 | A formally verified component that may support a new method-specific mathematical claim, subject to the evidence gates below |

There are 79 passing targets with an explicit naming/claim warning: 59 are generic headline-namespace warnings, with additional statement-only, premise-equivalence, collision, and contamination cases.

## PR #1: represented quantum-computing completions

All 34 listed targets are represented by exact current PR-ready files and map to passing AXLE records. Classification: **14 routine formalizations**, **20 useful library results**, **0 potentially research-significant mathematical results**.

| Target | Classification | Exact theorem/declaration |
| --- | --- | --- |
| `QC.no_cloning` | useful library result | `theorem no_cloning_of_inner_preserving (U : HH → HH) (hU : ∀ x y : HH, inner ℂ (U x) (U y) = inner ℂ x y) (hclone : ∀ ψ : H, ‖ψ‖ = 1 → U (tens ψ q0) = tens ψ ψ) : False` |
| `QC.pauli_anticommute` | useful library result | `theorem pauli_anticommute : pauliX * pauliY + pauliY * pauliX = 0 ∧ pauliY * pauliZ + pauliZ * pauliY = 0 ∧ pauliX * pauliZ + pauliZ * pauliX = 0 ∧ pauliX * pauliX = 1 ∧ pauliY * pauliY = 1 ` |
| `QC.pauli_basis` | useful library result | `theorem pauli_basis : LinearIndependent ℂ pauli ∧ Submodule.span ℂ (Set.range pauli) = ⊤ :=` |
| `QC.hadamard_involutive` | useful library result | `theorem hadamard_involutive : hadamard.conjTranspose = hadamard ∧ hadamard * hadamard = 1` |
| `QC.hadamard_XZ` | useful library result | `theorem hadamard_XZ : H * X * H = Z` |
| `QC.cnot_unitary_involutive` | useful library result | `theorem cnot_unitary_involutive : QC.CNOT.conjTranspose * QC.CNOT = 1 ∧ QC.CNOT * QC.CNOT.conjTranspose = 1 ∧ QC.CNOT * QC.CNOT = 1` |
| `QC.bell_orthonormal` | useful library result | `theorem bell_orthonormal : Orthonormal ℂ bell ∧ Submodule.span ℂ (Set.range bell) = ⊤` |
| `QC.chsh_tsirelson` | useful library result | `theorem chsh_tsirelson (T : IsCHSHTuple A₀ A₁ B₀ B₁) : ‖chshOp A₀ A₁ B₀ B₁‖ ≤ 2 * Real.sqrt 2` |
| `QC.teleportation_identity` | useful library result | `theorem teleportation_identity (psi : Qubit) (m₁ m₂ : Fin 2) : bobFinal psi m₁ m₂ = psi` |
| `QC.deutsch_correct` | useful library result | `theorem deutsch_correct (f : Bool → Bool) : (f false = f true → probZero f = 1 ∧ probOne f = 0) ∧ (f false ≠ f true → probZero f = 0 ∧ probOne f = 1)` |
| `QC.density_matrix_unitary_invariant` | useful library result | `theorem density_matrix_unitary_invariant {n : Type*} [Fintype n] [DecidableEq n] (ρ U : Matrix n n ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) (hU : U ∈ Matrix.unitaryGroup n ℂ) : (U * ρ * Uᴴ` |
| `QC.pure_state_zero_entropy` | useful library result | `theorem pure_state_zero_entropy (psi : n → ℂ) (hpsi : ∑ i, ‖psi i‖ ^ 2 = 1) : vonNeumannEntropy (isHermitian_pureState psi) = 0 :=` |
| `QC.qft_unitary` | useful library result | `theorem qft_unitary (n : ℕ) : qft n ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :=` |
| `QC.superdense_two_bits` | useful library result | `theorem superdense_two_bits : Function.Injective encode` |
| `QC.toffoli_unitary` | useful library result | `theorem toffoli_unitary : toffoli = toffoliPerm.permMatrix ℂ ∧ toffoli ∈ Matrix.unitaryGroup Q3 ℂ ∧ toffoliᴴ * toffoli = 1 ∧ toffoli * toffoliᴴ = 1 ∧ toffoli * toffoli = 1` |
| `QC.robertson_uncertainty` | useful library result | `theorem robertson_uncertainty {A B : H →ₗ[ℂ] H} (hA : IsSymm A) (hB : IsSymm B) {ψ : H} (hψ : ‖ψ‖ = 1) : Delta A ψ * Delta B ψ ≥ (1 / 2) * ‖expect (comm A B) ψ‖` |
| `QC.ghz3_normalized` | routine formalization | `theorem ghz3_normalized : ‖ghz3‖ = 1` |
| `QC.bloch_sphere_bijection` | useful library result | `theorem bloch_sphere_bijection : Function.Bijective bloch` |
| `QC.kraus_trace_preserving` | useful library result | `theorem kraus_trace_preserving {n K : Type*} [Fintype n] [DecidableEq n] [Fintype K] (E : K → Matrix n n ℂ) (hE : ∑ k, (E k)ᴴ * E k = 1) (ρ : Matrix n n ℂ) : (∑ k, E k * ρ * (E k)ᴴ).trace = ` |
| `QC.ghz_nonlocal` | useful library result | `theorem ghz_nonlocal : ¬ ∃ A B C : Setting → ℤ, ∀ s₁ s₂ s₃ : Setting, merminContext s₁ s₂ s₃ → (triObs s₁ s₂ s₃).mulVec ghz = ((A s₁ * B s₂ * C s₃ : ℤ) : ℂ) • ghz` |
| `QC.swap_test_overlap` | useful library result | `theorem swap_test_overlap (psi phi : ι → ℂ) (hpsi : ∑ i, ‖psi i‖ ^ 2 = 1) (hphi : ∑ i, ‖phi i‖ ^ 2 = 1) : acceptProb psi phi = (1 + ‖overlap psi phi‖ ^ 2) / 2` |
| `QC.qft_unitary_2` | routine formalization | `theorem qft_unitary_2 : qft2 ∈ Matrix.unitaryGroup (Fin 4) ℂ` |
| `QC.ghz2_normalized` | routine formalization | `theorem ghz2_normalized : ‖ghz2‖ = 1` |
| `QC.qft_unitary_3` | routine formalization | `theorem qft_unitary_3 : qft3 ∈ Matrix.unitaryGroup (Fin 8) ℂ :=` |
| `QC.qft_unitary_4` | routine formalization | `theorem qft_unitary_4 : qft4 ∈ Matrix.unitaryGroup (Fin 16) ℂ` |
| `QC.ghz4_normalized` | routine formalization | `theorem ghz4_normalized : ‖ghz4‖ = 1` |
| `QC.qft_unitary_5` | routine formalization | `theorem qft_unitary_5 : qftMatrix (2 ^ 5) ∈ Matrix.unitaryGroup (Fin (2 ^ 5)) ℂ :=` |
| `QC.ghz5_normalized` | routine formalization | `theorem ghz5_normalized : ‖ghz5‖ = 1` |
| `QC.qft_unitary_6` | routine formalization | `theorem qft_unitary_6 : qft6 ∈ Matrix.unitaryGroup (Fin 64) ℂ` |
| `QC.ghz6_normalized` | routine formalization | `theorem ghz6_normalized : ‖ghz6‖ = 1` |
| `QC.qft_unitary_7` | routine formalization | `theorem qft_unitary_7 : qftMatrix (2 ^ 7) ∈ Matrix.unitaryGroup (Fin (2 ^ 7)) ℂ :=` |
| `QC.ghz7_normalized` | routine formalization | `theorem ghz7_normalized : ‖ghz7‖ = 1` |
| `QC.qft_unitary_8` | routine formalization | `theorem qft_unitary_8 : qftMatrix (2 ^ 8) ∈ Matrix.unitaryGroup (Fin (2 ^ 8)) ℂ :=` |
| `QC.ghz8_normalized` | routine formalization | `theorem ghz8_normalized : ‖ghz8‖ = 1` |

Claim-safe summary: PR #1 is a compact formalization corpus of known QC results. Its strongest announcement angle is the independently AXLE-checked collection and reusable API—not “first Lean quantum formalization” and not new quantum mathematics. Existing primary repositories include [Physlib](https://github.com/leanprover-community/physlib), [Lean-QuantumInfo](https://github.com/Timeroot/Lean-QuantumInfo), [LeanQuantum](https://github.com/inQWIRE/LeanQuantum), [QECLean](https://github.com/Stavan-Jain/QECLean), and the Coq [QWIRE](https://github.com/inQWIRE/QWIRE).

## PR #2: represented cross-domain completions

All 147 retained targets are represented by exact current PR-ready files and map to passing AXLE records. Classification: **73 routine formalizations**, **74 useful library results**, **0 potentially research-significant mathematical results**.

The removed `Chem.huckel_C15` and `Chem.huckel_C19` files remain excluded because their current AXLE records fail. The most important PR #2 claim controls are the finite-model `Frontier.RH_Li_criterion`, the statement-only `Frontier.P_vs_NP_statement`, and the target-name collision around `Brockian.ConstellationLocalCountK3`.

## Potentially research-significant verified components

These three theorems form **one candidate family**, not three independent novelty claims. Both account streams reported `PROVED` jobs for each; the selected admin sources pass AXLE.

| Target | Accounts with PROVED job | Exact theorem | Classification |
| --- | --- | --- | --- |
| `Zeta23Obstruction.repaired_witness_nonneg` | admin, chris | `theorem repaired_witness_nonneg (x : ℝ) : 0 ≤ (Real.sin (Real.pi * x) / (Real.pi * x)) ^ 2 * (1 - (1 / 10) * Real.cos (3 * Real.pi * x))` | potentially research-significant |
| `Zeta23Obstruction.repaired_witness_neg_at_deep_point` | admin, chris | `theorem repaired_witness_neg_at_deep_point : (Real.sinh (2 * Real.pi) / (2 * Real.pi)) ^ 2 * (1 - (1 / 10) * Real.cosh (6 * Real.pi)) < 0` | potentially research-significant |
| `Zeta23Obstruction.tent_combination_neg_on_band` | admin, chris | `theorem tent_combination_neg_on_band {a : ℝ} (h1 : 1 < a) (h2 : a < 5 / 2) : T a - (1 / 20) * (T (a - 3 / 2) + T (a + 3 / 2)) < 0` | potentially research-significant |

## Naming and claim overreach

| Target/system | Risk | Claim-safe wording/action |
| --- | --- | --- |
| `aristotle/novelty_gate.py` | Absence of a distinctive Mathlib declaration-name match was printed as `NOVEL`. | Rename it as a scoped Mathlib-name overlap check; require literature and repository comparison for novelty. |
| `Brockian.RiemannScaffold.RH_of_BrockianSystem` | The premise `Nonempty BrockianSystem` is proved equivalent to RH in the same file. | Call this an equivalent-premise reduction, not progress on RH. |
| `Brockian.GoldbachSchema.goldbach_from_spectral_model` | `SpectralPositivity` is proved equivalent to the Goldbach representation count being nonzero. | Call this a spectral reformulation/equivalence, not progress on Goldbach. |
| `D5_card_verified` | The selected theorem is only `Fintype.card D5 = 10`, while project/header text claims an RH-spine result. | Separate and rename the D5 cardinality target; treat the conditional RH theorem by its exact spectral-realization premise. |
| `D5_card` / `D5.card` | Sanitizer collision produces the same `D5_card.lean` path. | Use a collision-resistant filename (for example target plus project UUID/hash). |
| `Brockian.ConstellationLocalCountK3` | A distinct unpublished arithmetic-progression job reused the same target name. | Keep the selected residue-avoidance theorem; rename the other result before ingestion. |
| `Frontier.RH_Li_criterion` | The theorem is for a finite symmetric family of zeros, not the classical infinite Li criterion. | Name it `finite_symmetric_zero_Li_criterion` or equivalent. |
| `Frontier.P_vs_NP_statement` | The headline object is a definition plus elementary consequences; it does not prove P ≠ NP. | Label it a P/NP definitions-and-scaffolding file. |
| Statement/reflexive targets | Examples include `Twin.conjecture_statement` and `Goldbach.conjecture_statement`, each essentially `P ↔ P`. | Classify as statement formalization only; never report the conjecture as proved. |
| Headline `Frontier.*` names | 59 verified files require exact-statement review; some assume the named theorem or prove a toy/special/finite form. | Public claims must quote the exact theorem signature and hypotheses. |

## Three strongest routes

| Route | Candidate | What is verified now | Evidence required before novelty/progress claim |
| --- | --- | --- | --- |
| Paper candidate | Zeta-23 repaired-witness obstruction family | Three AXLE-passing global lemmas establish real-line nonnegativity, negativity at the analytically continued point `2i`, and negativity of the Fourier tent combination on `(1, 5/2)`. | Formalize `subclass_obstruction_statement`; connect the normalized Lean kernel to the actual certificate transform; prove the result defeats a precisely cited class of methods; complete `damage_cost_exponent_law` and `sq_factor_lower_bound`; obtain independent analytic-number-theory review, literature search, pinned rebuild, and per-theorem axiom reports. |
| Technical announcement | 181-proof release corpus, led by PR #1’s 34 quantum-computing files | PR #1 is a compact AXLE-verified corpus of known QC results; PR #2 adds 147 verified cross-domain/library results. This is release engineering and formal-library work, not new mathematics. | Compare theorem by theorem with Physlib/Lean-QuantumInfo, LeanQuantum, QECLean, and QWIRE; document what is actually new as a Lean API/formalization; run an independent pinned build; save complete axiom output; clean namespaces and provenance/licensing; obtain external maintainer review. |
| Deeper research program | Brockian spectral/Riemann program | The current verified files provide scaffolds and conditional reductions, but the strongest RH implication assumes a spectral realization or a premise equivalent to RH. | Construct a noncircular spectral object; discharge at least one honest analytic bridge such as the Christoffel-count or ceiling bridge; publish a dependency graph showing no premise is equivalent to the conclusion; reproduce independently; get specialist review before any RH-progress language. |

## Parked candidates from the earlier top-three ledger

`Math2.kahn_kalai`, `CS.hilbert10_undecidable`, and `CS.blum_speedup` remain **PARTIAL**. The expanded harvest still contains no selected source bundle or AXLE record for any of them. They should not be promoted until the exact sources are ingested and independently checked.

## Release decision

- PR #1 and PR #2 are technically releaseable at the stated **AXLE-verified formalization** level after the wording correction about axiom reporting.
- Neither PR supports a mathematical-novelty claim.
- The Zeta-23 obstruction family is the only current passing family that merits a paper-oriented novelty investigation.
- The Riemann material should be presented as a research program with open bridges, not as progress on RH until a noncircular bridge is discharged.
- GitHub Actions currently fails before runner steps are assigned. It is an infrastructure failure and is not counted as proof verification; it also means Actions supplies no independent rebuild yet.

## Appendix A — all 717 AXLE-passing selected targets

| Target | Class | Account | Tier | AXLE hash | PR | Claim flag |
| --- | --- | --- | --- | --- | --- | --- |
| `AdditiveComb.cauchy_davenport_Z5` | routine formalization | chris | FRONTIER-wave2 | `7368324efe2455b7` |  |  |
| `AdditiveComb.freiman_two_A` | routine formalization | admin | FRONTIER-wave2 | `1745a6a47a7b8e64` |  |  |
| `AdditiveComb.plunnecke_ruzsa_shadow` | routine formalization | admin | FRONTIER-wave2 | `b791979db3df921f` |  |  |
| `AdditiveComb.schur_five` | routine formalization | chris | FRONTIER-wave2 | `18cdb44e50433d86` |  |  |
| `AdditiveComb.sumset_lower_bound` | routine formalization | chris | FRONTIER-wave2 | `0b6fb55932deb1c4` |  |  |
| `Algebra.fundamental_theorem_of_algebra` | routine formalization | admin | FRONTIER-wave2 | `376d9524cd4b7c16` |  |  |
| `Analysis.extreme_value` | routine formalization | admin | FRONTIER-wave2 | `5abe6a44beeaeb16` |  |  |
| `Analysis.intermediate_value` | routine formalization | chris | FRONTIER-wave2 | `f580de50fb5a5ec5` |  |  |
| `Aristotle.Prove_10_conjectures_relati` | routine formalization | chris | External | `a6deab03390f9320` |  |  |
| `Aristotle.Prove_that_the_Brockian_Rot` | routine formalization | chris | Brockian-external | `7ced7abab5a23bc0` |  |  |
| `Aristotle.Summarize_the_content_of_pr` | routine formalization | chris | External | `aa5aaa307ef4083c` |  |  |
| `bridge` | routine formalization | chris | Brockian-external | `52f7b17ef16a7a5e` |  |  |
| `Brock.GoldenRatio.sqrt5_pos` | routine formalization | chris | External | `4f68d7d465de2dc0` |  |  |
| `Brock.mem_translate_iff` | routine formalization | chris | External | `0a71be52ae0bb535` |  |  |
| `Brockian.AdmissibilityKTupleK4` | useful library result | admin | C-corpus-extension | `8ed244fbb7f644f1` | 2 |  |
| `Brockian.AmicableNumbers.AmicableInfinitude` | routine formalization | admin | B-conjecture | `0b071d005d927fde` |  |  |
| `Brockian.AndricaConjecture.AndricaConjecture` | routine formalization | chris | B-conjecture | `038dccd42987d739` |  | headline theorem supplied as a premise |
| `Brockian.BetrothedNumbers.betrothed_5775_6128` | routine formalization | admin | FRONTIER-betrothed | `32acffb8d39bd52e` |  |  |
| `Brockian.BetrothedNumbers.BetrothedInfinitude` | routine formalization | admin | B-conjecture | `6e9be2fc82991a80` |  |  |
| `Brockian.BetrothedNumbers.coprime_pair_four_primeFactors` | routine formalization | chris | FRONTIER-betrothed | `9a74a0fc2bc28b2d` |  |  |
| `Brockian.BetrothedNumbers.coprime_sameParity_twentyOne_primeFactors` | routine formalization | chris | FRONTIER-betrothed | `316b986d08ad3610` |  |  |
| `Brockian.BetrothedNumbers.density_zero_reduction` | routine formalization | chris | FRONTIER-betrothed | `8c06b4e841b2e876` |  |  |
| `Brockian.BetrothedNumbers.Dynamics.isBetrothedPair_iff_nontrivial_twoCycle` | routine formalization | chris | FRONTIER-betrothed | `74e675464a54df98` |  |  |
| `Brockian.BetrothedNumbers.Dynamics.thabit_balance_identity` | routine formalization | chris | FRONTIER-betrothed | `b0f03880852e0f78` |  |  |
| `Brockian.BetrothedNumbers.no_pair_of_mersenne_and_shifted_prime` | routine formalization | admin | FRONTIER-betrothed | `597e123e8b8eadc6` |  |  |
| `Brockian.BetrothedNumbers.primePower_member_structure` | routine formalization | chris | FRONTIER-betrothed | `5e9e3f5905cd7f40` |  |  |
| `Brockian.BetrothedNumbers.SameParityBetrothedExists` | routine formalization | admin | B-conjecture | `dce016a0924dd97e` |  |  |
| `Brockian.BrocardGap.BrocardGapConjecture` | routine formalization | admin | B-conjecture | `ff7d444522d94ac4` |  |  |
| `Brockian.BrocardProblem.BrocardConjecture` | routine formalization | chris | B-conjecture | `cf31adcb6530f6a5` |  |  |
| `Brockian.brockian_multiplicity_one` | routine formalization | chris | Brockian-external | `fc76f210dfa47385` |  |  |
| `Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude` | routine formalization | admin | B-conjecture | `78ac77f6001412df` |  |  |
| `Brockian.Cassini.cassini` | routine formalization | chris | Brockian-external | `d59ab2b29ec0605c` |  |  |
| `Brockian.CatalanClosed.succ_mul_catalan_eq_choose` | routine formalization | chris | Brockian-external | `79e6a1213a04519a` |  |  |
| `Brockian.Cayley.forestFinset_self` | routine formalization | chris | Brockian-external | `0bbe5d30b3f1a47b` |  |  |
| `Brockian.CollatzPartial.CollatzConjecture` | routine formalization | chris | B-conjecture | `59fc4880fdac3cb7` |  |  |
| `Brockian.const_of_transitive_invariant` | routine formalization | admin | Brockian-external | `ae70cbe5814b0df2` |  |  |
| `Brockian.ConstellationLocalCountK3` | useful library result | chris | C-corpus-extension | `4712b77b344fd68e` | 2 | same target name was used by a distinct Aristotle job; rename unpublished AP-count result |
| `Brockian.CosTraceNorm1279` | useful library result | admin | C-corpus-extension | `c45b2e9129284f2c` | 2 |  |
| `Brockian.CosTraceNorm1597` | useful library result | admin | C-corpus-extension | `a084d40ef5339ee6` | 2 |  |
| `Brockian.CosTraceNorm2003` | useful library result | admin | C-corpus-extension | `1b9aed2b8a67b44d` | 2 |  |
| `Brockian.CosTraceNorm2707` | useful library result | admin | C-corpus-extension | `2d65031faf9416ce` | 2 |  |
| `Brockian.CosTraceNorm3001` | useful library result | admin | C-corpus-extension | `03bb4d7a2e843d0f` |  |  |
| `Brockian.CosTraceNorm3499` | useful library result | chris | C-corpus-extension | `98e757240b56af10` | 2 |  |
| `Brockian.CosTraceNorm4001` | useful library result | chris | C-corpus-extension | `f6574af16c569ad4` |  |  |
| `Brockian.CullenWoodall.CullenPrimeInfinitude` | routine formalization | admin | B-conjecture | `c246efc2681f9401` |  |  |
| `Brockian.CullenWoodall.WoodallPrimeInfinitude` | routine formalization | chris | B-conjecture | `c179c6ca62254ba3` |  |  |
| `Brockian.D5.allElements_complete` | routine formalization | chris | Brockian-external | `9645d45d83550d5c` |  |  |
| `Brockian.Dilworth.ChainColoring.mono` | routine formalization | chris | Brockian-external | `539eac0b8273bcda` |  |  |
| `Brockian.EgyptianFraction.egyptian_fraction` | routine formalization | chris | Brockian-external | `c8e98d48b82dfec5` |  |  |
| `Brockian.Equidistribution.equidistribution_of_asymptotic_exists` | useful library result | chris | A2-discharge-open | `e047e272d9b7ae34` |  |  |
| `Brockian.Equidistribution.integrable_of_continuousMap` | useful library result | chris | Brockian-external | `65e1261086b88e80` |  |  |
| `Brockian.Equidistribution.integral_fourier` | useful library result | chris | Brockian-external | `ef63fd5ba197085d` |  |  |
| `Brockian.Equidistribution.integral_fourier_ne_zero` | useful library result | admin | Brockian-external | `06c01109aa339f8a` |  |  |
| `Brockian.EquidistributionBVReduction.configCount_density_of_BV` | useful library result | admin | A1-discharge-literature | `be4cf2cdbd2006f6` | 2 |  |
| `Brockian.EquidistributionBVReduction.configCount_over_main_tendsto` | useful library result | chris | A1-discharge-literature | `44c0c13307a71258` | 2 |  |
| `Brockian.EquidistributionBVReduction.geom_avg_tendsto` | useful library result | admin | Brockian-external | `e3a7a130cdb3c2f1` |  |  |
| `Brockian.EquidistributionBVReduction.total_over_main_tendsto` | useful library result | admin | A1-discharge-literature | `2aa6b455ce3e9248` |  |  |
| `Brockian.EquidistributionUniformity.equidistribution_of_transitive_symmetry` | useful library result | chris | A1-discharge-literature | `dffffac45bc1e480` | 2 |  |
| `Brockian.EquidistributionUniformity.measure_singleton_eq_of_transitive` | useful library result | admin | Brockian-external | `7ed6fb19dfee661f` |  |  |
| `Brockian.EquidistributionUniformity.sing_uniform_of_transitive` | useful library result | admin | A1-discharge-literature | `c77add9d5bfdae8f` | 2 |  |
| `Brockian.EquidistributionUniformity.singleton_measure_eq_of_transitive` | useful library result | chris | Brockian-external | `f5b15f736955268f` |  |  |
| `Brockian.ErdosGinzburgZiv.erdos_ginzburg_ziv` | routine formalization | chris | Brockian-external | `52669eca9cbea3cf` |  |  |
| `Brockian.ErdosStraus.ErdosStrausConjecture` | routine formalization | chris | B-conjecture | `ffb6216212b3b5e5` |  | statement/definition only |
| `Brockian.ErdosSzekeres.erdos_szekeres` | routine formalization | chris | Brockian-external | `668860446d6ca682` |  |  |
| `Brockian.EvenPerfectLastDigit.perfect_two_pow_mul_odd` | routine formalization | chris | Brockian-external | `61b5ee274a6ca5da` |  |  |
| `Brockian.EvenPerfectTriangular.sigma_two_pow_eq_mersenne_succ` | routine formalization | chris | Brockian-external | `c785be1e2fee0a0a` |  |  |
| `Brockian.EvenSuperperfect.sigma_two_pow_eq_mersenne_succ` | routine formalization | chris | Brockian-external | `d40b601c205ea69c` |  |  |
| `Brockian.FermatNumbers.FermatPrimeBeyondFour` | routine formalization | admin | B-conjecture | `bd684216cd9ffbdb` |  |  |
| `Brockian.FibGcd.fib_gcd` | routine formalization | chris | Brockian-external | `4a4f101b1f424e33` |  |  |
| `Brockian.FortunateNumbers.FortuneConjecture` | routine formalization | admin | B-conjecture | `99b0f3f916317139` |  |  |
| `Brockian.FreshmanDream.freshman_dream` | routine formalization | chris | Brockian-external | `bb74d23df671bf99` |  |  |
| `Brockian.FrobeniusAbove.frobenius_above` | routine formalization | chris | Brockian-external | `a9c16a76d0ebf272` |  |  |
| `Brockian.FrobeniusMcNugget.frobenius_not_representable` | routine formalization | chris | Brockian-external | `a61fcd1734964d62` |  |  |
| `Brockian.GaussWilson.prod_units_sq_eq_one` | routine formalization | chris | Brockian-external | `de3d95103cee9c13` |  |  |
| `Brockian.GilbreathConjecture.GilbreathConjecture` | routine formalization | admin | B-conjecture | `ef412e4a1a448854` |  |  |
| `Brockian.GiugaNumbers.OddGiugaExists` | routine formalization | chris | B-conjecture | `809f1392f074f455` |  |  |
| `Brockian.GoldbachComb.gCount_eq` | routine formalization | chris | Brockian-external | `5569a01e0800fd6f` |  |  |
| `Brockian.GoldbachComb.GoldbachCovarianceTransfer` | routine formalization | admin | B-conjecture | `d54d710736e0a9e3` |  |  |
| `Brockian.GoldbachSchema.goldbach_beyond_of_model` | useful library result | admin | A2-discharge-open | `79fe7e719f823e57` |  |  |
| `Brockian.GoldbachSchema.goldbach_from_spectral_model` | useful library result | admin | A2-discharge-open | `154d82f6992e52fd` |  | spectral predicate is proved equivalent to Goldbach; not progress on Goldbach |
| `Brockian.GoldbachSchema.integral_chr` | useful library result | chris | Brockian-external | `e762f5ce9d5b894d` |  |  |
| `Brockian.GoldbachWheelK2_1051` | routine formalization | admin | C-corpus-extension | `853880f90f73c52d` | 2 |  |
| `Brockian.GoldbachWheelK2_1153` | routine formalization | chris | C-corpus-extension | `78f6dca4d7ada4ab` | 2 |  |
| `Brockian.GoldbachWheelK2_1327` | routine formalization | admin | C-corpus-extension | `bb0762f2fe4a5e2a` | 2 |  |
| `Brockian.GoldbachWheelK2_631` | routine formalization | admin | C-corpus-extension | `7d717bc9b968765a` | 2 |  |
| `Brockian.GoldbachWheelK2_727` | routine formalization | chris | C-corpus-extension | `bfa35916aa628a64` | 2 |  |
| `Brockian.GoldbachWheelK2_947` | routine formalization | chris | C-corpus-extension | `c8f6500cb9aebdd5` | 2 |  |
| `Brockian.HockeyStick.hockey_stick` | routine formalization | chris | Brockian-external | `7af2bd334f46c17a` |  |  |
| `Brockian.HyperperfectNumbers.HyperperfectAllK` | routine formalization | admin | B-conjecture | `b60c4f96d491538b` |  |  |
| `Brockian.HyperperfectNumbers.HyperperfectInfinitude` | routine formalization | chris | B-conjecture | `91a2c2273694bed0` |  |  |
| `Brockian.KummerTheorem.kummer` | routine formalization | chris | Brockian-external | `f4d8f6df33ee820a` |  |  |
| `Brockian.LteTwo.emult_two_pow_sub_pow` | routine formalization | chris | Brockian-external | `843add0b34411fa1` |  |  |
| `Brockian.LucasTheorem.lucas` | routine formalization | chris | Brockian-external | `75d90f7d76cef403` |  |  |
| `Brockian.MasonStothers.natDegree_radical_le_card_roots` | routine formalization | chris | Brockian-external | `776268848b1cf75a` |  |  |
| `Brockian.MersennePerfect.EvenPerfectInfinitude` | routine formalization | chris | B-conjecture | `03abdf6977e29903` |  |  |
| `Brockian.MsBeatty.beatty` | routine formalization | chris | Brockian-external | `cdd41928d0722146` |  |  |
| `Brockian.MsBinet.binet` | routine formalization | chris | Brockian-external | `48f05895fd0a6651` |  |  |
| `Brockian.MsBirkhoff.birkhoff_von_neumann` | routine formalization | chris | Brockian-external | `7f7cd28c7e552da8` |  |  |
| `Brockian.MsBritishFlag.british_flag` | routine formalization | chris | Brockian-external | `09df7313dc5de122` |  |  |
| `Brockian.MsCatalanSquareSum.sum_choose_sq` | routine formalization | chris | Brockian-external | `3a7f99118f0f21b9` |  |  |
| `Brockian.MsCauchyDavenport.cauchy_davenport` | routine formalization | chris | Brockian-external | `baefe4e4fa243992` |  |  |
| `Brockian.MsCeva.indep_of_not_collinear` | routine formalization | chris | Brockian-external | `fadc65c76114e5fb` |  |  |
| `Brockian.MsChebyshevSum.chebyshev_sum` | routine formalization | chris | Brockian-external | `4d6506ed7f3e884a` |  |  |
| `Brockian.MsChebyshevTheta.chebyshev_theta` | routine formalization | chris | Brockian-external | `50d5efa5f2da2960` |  |  |
| `Brockian.MsDerangement.derangement_closed` | routine formalization | chris | Brockian-external | `866ad86cb3bdcf21` |  |  |
| `Brockian.MsE2Irrational.exp_two_irrational` | routine formalization | chris | Brockian-external | `e3a8873c38707fc4` |  |  |
| `Brockian.MsErdosAnning.quad_three_roots` | routine formalization | chris | Brockian-external | `2bc3c5332ba9794d` |  |  |
| `Brockian.MsEulerPentagonal.restricted_true` | routine formalization | chris | Brockian-external | `ab45fa881c16e51f` |  |  |
| `Brockian.MsFrobeniusGeneral.two_gen_rep` | routine formalization | chris | Brockian-external | `0bf9d28085cc229e` |  |  |
| `Brockian.MsFrobeniusGroup.sol_eq_solEq_one` | routine formalization | chris | Brockian-external | `65d85412c13a800e` |  |  |
| `Brockian.MsGaussLucas.gauss_lucas` | routine formalization | chris | Brockian-external | `c5f624a7694b3e49` |  |  |
| `Brockian.MsGaussSum.gauss_sum_abs_sq` | routine formalization | chris | Brockian-external | `ab3a498bbb46f43a` |  |  |
| `Brockian.MsHermiteHadamard.hh_le_max` | routine formalization | chris | Brockian-external | `55c10a8f658108d6` |  |  |
| `Brockian.MsHeron.heron` | routine formalization | chris | Brockian-external | `de92e5c05a890888` |  |  |
| `Brockian.MsLagrangeIdentity.lagrange_identity` | routine formalization | chris | Brockian-external | `47859bdf47fdd817` |  |  |
| `Brockian.MsLYM.lym` | routine formalization | chris | Brockian-external | `4c98f6b20bc44bf8` |  |  |
| `Brockian.MsMachin.machin` | routine formalization | chris | Brockian-external | `c32f775f8a993576` |  |  |
| `Brockian.MsMenelaus.indep_of_not_collinear` | routine formalization | chris | Brockian-external | `5d03aef06f1d71ec` |  |  |
| `Brockian.MsMirsky.height_filter_nonempty` | routine formalization | chris | Brockian-external | `9ef96f8ac071301b` |  |  |
| `Brockian.MsNapoleon.napoleon` | routine formalization | chris | Brockian-external | `4e62bbc46314cd6b` |  |  |
| `Brockian.MsPell.pell_solvable` | routine formalization | chris | Brockian-external | `9ece1a215a184a2e` |  |  |
| `Brockian.MsPepin.pepin` | routine formalization | chris | Brockian-external | `2247365a71acf32d` |  |  |
| `Brockian.MsPerronFrobenius.Kset_nonneg` | routine formalization | chris | Brockian-external | `e414fc1eb5eeb23d` |  |  |
| `Brockian.MsPocklington.pocklington` | routine formalization | chris | Brockian-external | `c51eba8929c675f7` |  |  |
| `Brockian.MsPrimitiveRootCount.primitive_root_count` | routine formalization | chris | Brockian-external | `2defe09063020622` |  |  |
| `Brockian.MsProth.proth` | routine formalization | chris | Brockian-external | `e6c5ee6e76044e85` |  |  |
| `Brockian.MsQrTwo.two_is_qr_iff` | routine formalization | chris | Brockian-external | `949078e7c30eba6a` |  |  |
| `Brockian.MsSchurInequality.schur_inequality` | routine formalization | chris | Brockian-external | `a7e6552ae2595359` |  |  |
| `Brockian.MsSchurInequality.schur_ordered` | routine formalization | chris | Brockian-external | `410b2e204103b08c` |  |  |
| `Brockian.MsStewart.stewart` | routine formalization | chris | Brockian-external | `7ffc936977cdb2eb` |  |  |
| `Brockian.MsThue.thue_lemma` | routine formalization | chris | Brockian-external | `9e669442fffa831f` |  |  |
| `Brockian.MsVanDerWaerden.van_der_waerden` | routine formalization | chris | Brockian-external | `895e86679bf55bfd` |  |  |
| `Brockian.MsViete.viete_product` | routine formalization | chris | Brockian-external | `9fd3cac43ac4f931` |  |  |
| `Brockian.MsViviani.ptolemy_inequality` | routine formalization | chris | Brockian-external | `db993b653247e557` |  |  |
| `Brockian.MsWilsonPrimePower.wilson_prime_power` | routine formalization | chris | Brockian-external | `140c11812245cc70` |  |  |
| `Brockian.MsZeckendorf.pairwise_of_isZeckendorfRep` | routine formalization | chris | Brockian-external | `1356eaf87fc703ac` |  |  |
| `Brockian.Nicomachus.sq_sum_eq_sum_cubes` | routine formalization | chris | Brockian-external | `b1839051c62f397d` |  |  |
| `Brockian.Niven.niven_cos` | routine formalization | chris | Brockian-external | `eb68cb111ce8763a` |  |  |
| `Brockian.OddPerfectEuler.oddPerfect_euler_form` | routine formalization | chris | Brockian-external | `1731876cfe8f311b` |  |  |
| `Brockian.OddPerfectThreePrimes.oddPerfect_three_primes` | routine formalization | chris | Brockian-external | `63bb837f465565a2` |  |  |
| `Brockian.OppermannConjecture.OppermannConjecture` | routine formalization | admin | B-conjecture | `121807bbb5173a21` |  |  |
| `Brockian.OreHarmonicNumbers.OddHarmonicExists` | routine formalization | admin | B-conjecture | `6de050336178a2cf` |  |  |
| `Brockian.PalindromicPrimes.PalindromicPrimeInfinitude` | routine formalization | chris | B-conjecture | `d234206dc76d6455` |  |  |
| `Brockian.PentagonPentagonCharacterMultiplicityExt` | useful library result | admin | C-corpus-extension | `99de7d645f6a2c79` | 2 |  |
| `Brockian.PentagonPentagonEquivarianceGeneral` | useful library result | admin | C-corpus-extension | `49ee05e7576090ed` | 2 |  |
| `Brockian.PentagonPentagonIsotypicHigherN` | useful library result | chris | C-corpus-extension | `5cd1fd59551ec2ef` | 2 |  |
| `Brockian.PerfectReciprocalSum.perfect_reciprocal_sum` | routine formalization | chris | Brockian-external | `f45afabe7fe39513` |  |  |
| `Brockian.PerfectTotient.PerfectTotientInfinitude` | routine formalization | admin | B-conjecture | `49640e4a13b9e5ea` |  |  |
| `Brockian.PhaseDepthTorus.rho_period` | routine formalization | chris | Brockian-external | `4150ffebdcd99d28` |  |  |
| `Brockian.phi_squared` | routine formalization | chris | Brockian-external | `7ac52205127be238` |  |  |
| `Brockian.PolignacPrimes.PolignacConjecture` | routine formalization | chris | B-conjecture | `8d0d3e26e490e16b` |  |  |
| `Brockian.PracticalNumbers.PracticalTwinInfinitude` | routine formalization | admin | B-conjecture | `f8a2271b6c026e25` |  |  |
| `Brockian.PseudoprimesBaseTwo.infinite_pseudoprimes_base_two` | routine formalization | chris | Brockian-external | `d70a64867f9bcb07` |  |  |
| `Brockian.RepunitPrimes.RepunitPrimeInfinitude` | routine formalization | chris | B-conjecture | `59f9edee38c1531a` |  |  |
| `Brockian.RiemannScaffold.RH_of_BrockianSystem` | routine formalization | admin | A2-discharge-open | `4ff49a2bb977371b` |  | premise is equivalent to RH; conditional reduction only |
| `Brockian.RieselCovering.RieselProblem` | routine formalization | admin | B-conjecture | `0b192e00a1403e11` |  |  |
| `Brockian.RuthAaronPairs.RuthAaronInfinitude` | routine formalization | admin | B-conjecture | `78fb2873de8bd2b3` |  |  |
| `Brockian.Schur.fR_pos` | routine formalization | chris | Brockian-external | `3420bdcb9fae3be3` |  |  |
| `Brockian.SierpinskiCovering.SierpinskiProblem` | routine formalization | chris | B-conjecture | `59c4d3bd8b3b8d1f` |  |  |
| `Brockian.SingularSeriesConvergenceRate` | routine formalization | chris | C-corpus-extension | `6ca98d21e67acc4f` |  |  |
| `Brockian.SingularSeriesGaps12401250` | routine formalization | admin | C-corpus-extension | `6cbd565d555fd0a5` | 2 |  |
| `Brockian.SingularSeriesGaps13501360` | routine formalization | chris | C-corpus-extension | `1201730b26958b3a` | 2 |  |
| `Brockian.SingularSeriesGaps14501460` | routine formalization | admin | C-corpus-extension | `37c50c840124c7b8` | 2 |  |
| `Brockian.SingularSeriesGaps16021610` | routine formalization | chris | C-corpus-extension | `c1c8da46b0282274` | 2 |  |
| `Brockian.SingularSeriesGaps7280` | routine formalization | admin | C-corpus-extension | `4c6289eb4b8082b2` | 2 |  |
| `Brockian.SingularSeriesGaps9098` | routine formalization | admin | C-corpus-extension | `3defdde08a38aa40` | 2 |  |
| `Brockian.SophieGermain.a4_add_4b4_not_prime` | routine formalization | chris | Brockian-external | `df196ecd197b4627` |  |  |
| `Brockian.SophieGermain.SophieGermainInfinitude` | routine formalization | chris | B-conjecture | `08b50193098e563e` |  |  |
| `Brockian.spectralParameter_isReal_iff` | routine formalization | admin | Brockian-external | `7881bc087436265a` |  |  |
| `Brockian.Sperner.sperner_card_le` | routine formalization | chris | Brockian-external | `bc17ed3a0742b2c0` |  |  |
| `Brockian.StarOfDavid.star_of_david` | routine formalization | chris | Brockian-external | `5718742027dfdd62` |  |  |
| `Brockian.SylvesterSchur.piCount_le_self` | routine formalization | chris | Brockian-external | `b3f527f1fe0d7c8d` |  |  |
| `Brockian.Turan.turan` | routine formalization | chris | Brockian-external | `a1ce9bdbe439f0c8` |  |  |
| `Brockian.TwinPrimes.TwinPrimeConjecture` | routine formalization | chris | B-conjecture | `f6e684589e1bfd3f` |  |  |
| `Brockian.TwoSquares.sum_two_squares_iff` | routine formalization | chris | Brockian-external | `1a9987e0d71082f2` |  |  |
| `Brockian.TwoSquaresUnique.two_squares_unique` | routine formalization | chris | Brockian-external | `35cf03b78d046b87` |  |  |
| `Brockian.UnitaryPerfect.SixthUnitaryPerfectExists` | routine formalization | chris | B-conjecture | `a35f649fae69a855` |  |  |
| `Brockian.Vandermonde.vandermonde` | routine formalization | chris | Brockian-external | `aca9650d479867e4` |  |  |
| `Brockian.volume_circ_univ` | routine formalization | chris | Brockian-external | `a15eaa2baec84526` |  |  |
| `Brockian.weight_const_of_transitive` | routine formalization | chris | Brockian-external | `ced2e49fa358cd7e` |  |  |
| `Brockian.Weyl.BoundedVTarget.dirichletPotential_solution_zero` | routine formalization | chris | Brockian-external | `c9e6fa453e519245` |  |  |
| `Brockian.Weyl.DeficiencyODE.deficiencyRepresentsODE_of_weakRegularity` | useful library result | admin | A1-discharge-literature | `966071a5398b4772` |  |  |
| `Brockian.Weyl.DeficiencyODE.WeakRegularity.of_continuous` | routine formalization | admin | Brockian-external | `3218bd93ec66c8d3` |  |  |
| `Brockian.Weyl.KatoTarget.isSelfAdjoint_add` | routine formalization | chris | Brockian-external | `20b9cde847387a87` |  |  |
| `Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_rvm` | routine formalization | chris | A2-discharge-open | `d1298b2b3436f6ce` |  |  |
| `Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_WeylLawMatch` | routine formalization | admin | A2-discharge-open | `4d3ba9d20e0c7cba` |  |  |
| `Brockian.Weyl.WeylLawTarget.counting_diverges_of_exists` | routine formalization | admin | A2-discharge-open | `bb02d0d58f975ad0` |  |  |
| `Brockian.Wolstenholme.wolstenholme` | routine formalization | chris | Brockian-external | `0cbc373ec7b3b437` |  |  |
| `Brockian.Zsygmondy.Phi_pos` | routine formalization | chris | Brockian-external | `a9b6039e2856a656` |  |  |
| `Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure` | routine formalization | chris | B-conjecture | `05fcabf5f4dd2763` |  |  |
| `BrockianFrontier.Gilbreath.gilbreath_rows_9_16` | routine formalization | chris | Brockian-external | `196117a14e8e1d6c` |  |  |
| `BrockianFrontier.PathSpectrum.H4_eigenvalue_golden` | routine formalization | chris | Brockian-external | `45703037efadb603` |  |  |
| `BrockianFrontier.PentagonSpectrum.C5_golden_eigenvalue` | routine formalization | chris | Brockian-external | `88003bb7b39c5eb8` |  |  |
| `BrockianFrontier.SieveK5.nu_le_card` | routine formalization | chris | Brockian-external | `0d45aeae6f619966` |  |  |
| `BrockianFrontier.SingularSeries.localFactor_pos_of_lt` | routine formalization | chris | Brockian-external | `53d7023dc7e718f9` |  |  |
| `BrockianMagnumOpus.φ_pos` | routine formalization | chris | Brockian-external | `70b67ba37a7a9582` |  |  |
| `BrockianQuantum.braid_relation_conj` | routine formalization | admin | Brockian-external | `70fc5c373b9dfce6` |  |  |
| `BrockianQuantum.clock_pow_card` | routine formalization | admin | Brockian-external | `a07449fba48d96f6` |  |  |
| `BrockianQuantum.CNOT_sq` | routine formalization | admin | Brockian-external | `b00c4bcdab6866bd` |  |  |
| `BrockianQuantum.E0_idem` | routine formalization | admin | Brockian-external | `1685024efff3db35` |  |  |
| `BrockianQuantum.F_symmetric` | routine formalization | admin | Brockian-external | `9c92b45e01683fd2` |  |  |
| `BrockianQuantum.fib_fusion_gold_eigenvalue` | routine formalization | admin | Brockian-external | `a5505ca7058cc5f1` |  |  |
| `BrockianQuantum.golden_eq` | routine formalization | admin | Brockian-external | `f387909896da765e` |  |  |
| `BrockianQuantum.H_sq` | routine formalization | admin | Brockian-external | `e40c6e676397ef97` |  |  |
| `BrockianQuantum.normSq_c` | routine formalization | admin | Brockian-external | `505f3162b37e5fce` |  |  |
| `BrockianQuantum.om_pow_five` | routine formalization | admin | Brockian-external | `d2c918f5b4d3312e` |  |  |
| `BrockianQuantum.P0_idem` | routine formalization | admin | Brockian-external | `1e1eaf2052beb8c7` |  |  |
| `BrockianQuantum.phiP_XX_eigen` | routine formalization | admin | Brockian-external | `b0ebfe3a2054716b` |  |  |
| `BrockianQuantum.PX_sq` | routine formalization | admin | Brockian-external | `f68ac8fddc7e2ea2` |  |  |
| `BrockianQuantum.qft_mul_conjTranspose` | routine formalization | admin | Brockian-external | `cf073375bdeb139b` |  |  |
| `BrockianQuantum.Rz_zero` | routine formalization | admin | Brockian-external | `1db7c0eab5d59199` |  |  |
| `BrockianQuantum.S_sq_eq_Z` | routine formalization | admin | Brockian-external | `85b6fac358d84bdf` |  |  |
| `BrockianQuantum.S_Z_commute` | routine formalization | admin | Brockian-external | `e55453ac9950cff8` |  |  |
| `BrockianQuantum.shift_pow_card` | routine formalization | admin | Brockian-external | `b95418190b5b5909` |  |  |
| `BrockianQuantum.shift_unitary` | routine formalization | admin | Brockian-external | `c62ed11daedbd11b` |  |  |
| `BrockianQuantum.Tof_sq` | routine formalization | admin | Brockian-external | `106263077e56cc4c` |  |  |
| `BrockianQuantum.W2_unitary` | routine formalization | admin | Brockian-external | `f59d7735e319c642` |  |  |
| `BrockianSieve.legendre_count` | routine formalization | admin | Brockian-external | `5988dca861bcaebc` |  |  |
| `BrockianSieve.legendre_sieve` | routine formalization | admin | Brockian-external | `85df6b813f8a7aa5` |  |  |
| `BrockianSieve.squarefree_count` | routine formalization | admin | Brockian-external | `2119e793883a5301` |  |  |
| `BrockianSieve.totient_eq_sum_moebius` | routine formalization | admin | Brockian-external | `49d43dd508fd0850` |  |  |
| `BSCS.UnitaryRep.Uop_mul` | routine formalization | chris | External | `2d0d88cdcb07aa16` |  |  |
| `C2.Alg3.cramer_solve` | routine formalization | chris | External | `14931d6acb2eecf5` |  |  |
| `C2.An4.ftc` | routine formalization | chris | External | `01009e0438f0d333` |  |  |
| `C2.BSpec3.P7_eigen_center` | routine formalization | chris | Brockian-external | `a545cbfa2a844031` |  |  |
| `C2.Comb3.sum_range_id` | routine formalization | chris | External | `320008db432a4680` |  |  |
| `C2.Crypto2.otp_bij` | routine formalization | admin | External | `e1f577fabfcc0a93` |  |  |
| `C2.CS2.no_universal_decider` | routine formalization | chris | External | `968758bcffefbf40` |  |  |
| `C2.Geo2.apollonius` | routine formalization | admin | External | `c26280dcba9e182a` |  |  |
| `C2.Graph2.degree_sum_edges` | routine formalization | admin | External | `f94c250a1afe3d1b` |  |  |
| `C2.IT3.entropy_term_bound` | routine formalization | admin | External | `2a26dec4d7d45064` |  |  |
| `C2.NT4.order_dvd_card` | routine formalization | admin | External | `b135d110ced7130e` |  |  |
| `C2.Phys3.spin_comm_xy` | routine formalization | admin | External | `6391dbb68f4d3e25` |  |  |
| `C2.Prob2b.markov_ineq` | routine formalization | admin | External | `b2eca3870062cfa5` |  |  |
| `C2.QI4.swap_involutive` | routine formalization | admin | External | `737c5f2a0e1ffdcb` |  |  |
| `C2.SetT.zorn` | routine formalization | admin | External | `092ddd7f8befad91` |  |  |
| `C2.Topo2.continuous_image_compact` | routine formalization | admin | External | `52ae0cdc42713c05` |  |  |
| `C3.Alg4.crt_ring` | routine formalization | chris | External | `510cc396d8bd363e` |  |  |
| `C3.An5.abel_summation` | routine formalization | admin | External | `50081c75e2e168d3` |  |  |
| `C3.BCon.twin_adm_count_bound` | routine formalization | chris | Brockian-external | `1b411e664e1dbe9a` |  |  |
| `C3.BD5.dihedral5_card` | routine formalization | admin | Brockian-external | `8a44158f454e1842` |  |  |
| `C3.BSieve4.nu_lt_nine` | routine formalization | chris | Brockian-external | `81326aac45012623` |  |  |
| `C3.BSpec4.P8_eigen_center` | routine formalization | admin | Brockian-external | `ea099da32c4a4d1c` |  |  |
| `C3.Comb4.stirling_second_recurrence` | routine formalization | chris | External | `e88b0bfb3632df73` |  |  |
| `C3.Graph3.complete_edges` | routine formalization | admin | External | `145074b8b7d66497` |  |  |
| `C3.LinAlg.gram_schmidt_orthonormal` | routine formalization | chris | External | `136114bc7102ded7` |  |  |
| `C3.Meas.measure_mono` | routine formalization | admin | External | `6f29eb96ea9165b4` |  |  |
| `C3.NT5.legendre_euler` | routine formalization | chris | External | `e0d3169c8f652147` |  |  |
| `C3.Phys4.number_op_diag` | routine formalization | admin | External | `0eafebbea3f1d999` |  |  |
| `C3.Prob3.chebyshev_ineq` | routine formalization | chris | External | `389e6fa84a1f91e1` |  |  |
| `C3.QC5.phase_kickback` | routine formalization | admin | External | `1b932560df2a82e5` |  |  |
| `C3.QI5.toffoli_involutive` | routine formalization | chris | External | `522e1c3a5514edf1` |  |  |
| `C3.RA6.cont_add` | routine formalization | admin | External | `f3e7e058842acdad` |  |  |
| `C3.Topo3.closed_inter_compact` | routine formalization | chris | External | `480fe9c8f7084a11` |  |  |
| `C4.Alg5.cayley_hamilton_field` | routine formalization | chris | External | `81964e16324f70bb` |  |  |
| `C4.BChar.dihedral_card` | routine formalization | chris | Brockian-external | `9be192a894b041a3` |  |  |
| `C4.BM3.pentagonal_pentagon_area` | routine formalization | admin | Brockian-external | `28c5ffda7256b4d2` |  |  |
| `C4.BS5.lf_pos_ten` | routine formalization | chris | Brockian-external | `64c808acc814847a` |  |  |
| `C4.BSp5.P9_eigen_center` | routine formalization | admin | Brockian-external | `7da31835b477bbc8` |  |  |
| `C4.Comb5.inclusion_exclusion_three` | routine formalization | chris | External | `8da06adab6d7d444` |  |  |
| `C4.G4.empty_graph_no_edges` | routine formalization | chris | External | `f35e21698a35fdfc` |  |  |
| `C4.Geo3.inner_self_nonneg` | routine formalization | admin | External | `d4a4d488bcf42348` |  |  |
| `C4.IT4.log_le_sub` | routine formalization | admin | External | `baa7e0893daec39f` |  |  |
| `C4.LA2.transpose_mul` | routine formalization | chris | External | `d3ee21048a0be167` |  |  |
| `C4.NT6.quadratic_reciprocity` | routine formalization | admin | External | `055bf04931673a14` |  |  |
| `C4.Phys5.comm_yz` | routine formalization | admin | External | `91c0915f75e15473` |  |  |
| `C4.Prob4.am_qm` | routine formalization | chris | External | `2073d0a0e8fe795f` |  |  |
| `C4.QC6.T_sq_eq_S` | routine formalization | chris | External | `d64bb94d441249f2` |  |  |
| `C4.RA7.abs_triangle` | routine formalization | chris | External | `c198579a93d9ebbb` |  |  |
| `C4.ST2.powerset_card` | routine formalization | admin | External | `10f854164a01ae80` |  |  |
| `C5.Alg6.ker_normal` | routine formalization | admin | External | `28af52ecddf85f86` |  |  |
| `C5.An7.continuous_polynomial` | routine formalization | chris | External | `2c589e9042cca9ed` |  |  |
| `C5.BS6.nu_lt_of_prime` | routine formalization | admin | Brockian-external | `22d5ea9841c4f48f` |  |  |
| `C5.BSp6.P10_symm` | routine formalization | chris | Brockian-external | `9119ef2ec0032160` |  |  |
| `C5.C6.sum_range_succ_id` | routine formalization | admin | External | `954d7cbcc2498236` |  |  |
| `C5.NT7.even_perfect_form` | routine formalization | admin | External | `5601270aed8d9b59` |  |  |
| `C5.Ph6.spin_total_sq` | routine formalization | admin | External | `abe31f9220be6f70` |  |  |
| `C5.QI7.ghz_norm` | routine formalization | admin | External | `ccdf6c1a8bda6094` |  |  |
| `C6.Alg7.subgroup_mul_mem` | routine formalization | chris | External | `6ca4ccc876c94281` |  |  |
| `C6.An8.deriv_cos` | routine formalization | admin | External | `3ac1e0f066dd132d` |  |  |
| `C6.BD6.golden_pow4` | routine formalization | chris | Brockian-external | `35da8734c436a357` |  |  |
| `C6.BS7.adm_37` | routine formalization | admin | Brockian-external | `dc271dec5632045a` |  |  |
| `C6.BSp7.C8_trace` | routine formalization | chris | Brockian-external | `c11460b54705066f` |  |  |
| `C6.C7.sum_sq_formula` | routine formalization | chris | External | `1146d31e7f48c309` |  |  |
| `C6.Geo4.norm_nonneg_v` | routine formalization | admin | External | `3042f18479b08538` |  |  |
| `C6.IT5.log_mul_pos` | routine formalization | chris | External | `7807709f9527767d` |  |  |
| `C6.NT8.sum_totient_divisors` | routine formalization | chris | External | `793bb682d36546d4` |  |  |
| `C6.P5.prob_sum_one` | routine formalization | admin | External | `e796e5d16d39bf1e` |  |  |
| `C6.QC7.xyz_eq_i` | routine formalization | admin | External | `04f4a9b0913316f1` |  |  |
| `C6.T4.union_open` | routine formalization | chris | External | `e9da4c6fd8a745bb` |  |  |
| `Cardinal.aleph_fixed_point_statement` | routine formalization | chris | FRONTIER-wave2 | `3defec81d045eba5` |  | statement/definition only |
| `Cardinal.continuum_eq_two_pow_aleph0` | routine formalization | chris | FRONTIER-wave2 | `0e51f5a3c35c2675` |  |  |
| `Chebyshev.psi_two_le` | routine formalization | chris | FRONTIER-wave2 | `70777a687beffe34` |  |  |
| `Chem.arrhenius_monotone` | useful library result | chris | DOMAIN-chem | `37196a856622c651` | 2 |  |
| `Chem.balance_nullspace` | useful library result | admin | DOMAIN-chem | `864fd0702754d479` | 2 |  |
| `Chem.benzene_D6h_irreps` | useful library result | admin | DOMAIN-chem | `8eebae1a7a5a2cf2` | 2 |  |
| `Chem.entropy_concave` | useful library result | chris | DOMAIN-chem | `8333596244361ca4` | 2 |  |
| `Chem.euler_polyhedron` | useful library result | chris | DOMAIN-chem | `a3fb3ba84fe410e8` | 2 |  |
| `Chem.fullerene_pentagons` | useful library result | chris | DOMAIN-chem | `1c716ed1ddb00bf9` | 2 |  |
| `Chem.gibbs_phase_rule` | useful library result | admin | DOMAIN-chem | `efb88f2ee1c37c8d` | 2 |  |
| `Chem.handshake_valence` | useful library result | chris | DOMAIN-chem | `8bf6e24dc2e2f73b` | 2 |  |
| `Chem.huckel_C10` | routine formalization | chris | DOMAIN-chem | `585c91074fca21a4` | 2 |  |
| `Chem.huckel_C12` | routine formalization | chris | DOMAIN-chem | `dbaa4893c7449e45` | 2 |  |
| `Chem.huckel_C17` | routine formalization | chris | DOMAIN-chem | `d9d51c72fea2002e` | 2 |  |
| `Chem.huckel_C18` | routine formalization | admin | DOMAIN-chem | `ca5b508de69c9676` | 2 |  |
| `Chem.huckel_C3` | routine formalization | chris | DOMAIN-chem | `f4e96eed5899eac9` | 2 |  |
| `Chem.huckel_C4` | routine formalization | admin | DOMAIN-chem | `6aba308bb94cff16` | 2 |  |
| `Chem.huckel_C5` | routine formalization | admin | DOMAIN-chem | `8aa59f8a8eef3887` | 2 |  |
| `Chem.huckel_C6` | routine formalization | chris | DOMAIN-chem | `44fc34c6f27789b2` | 2 |  |
| `Chem.huckel_C7` | routine formalization | chris | DOMAIN-chem | `18631dc625ed8460` | 2 |  |
| `Chem.leChatelier_sign` | useful library result | admin | DOMAIN-chem | `33645623c749e2e1` | 2 |  |
| `Chem.molecular_orbital_count` | useful library result | chris | DOMAIN-chem | `f613f31ccf43e07d` | 2 |  |
| `Chem.point_group_finite_O3` | useful library result | chris | DOMAIN-chem | `df289c231dfbe455` | 2 |  |
| `Chem.wiener_path_formula` | useful library result | admin | DOMAIN-chem | `1aad01b16b6ec650` | 2 |  |
| `Combinatorics.pigeonhole` | routine formalization | admin | FRONTIER-wave2 | `158084f12c5b9d47` |  |  |
| `Constellation.admissible_triple` | routine formalization | chris | FRONTIER-primes | `a354e885f629d970` |  |  |
| `Constellation.quadruplet_11_13_17_19` | routine formalization | admin | FRONTIER-primes | `a0d7c9099bacbfc6` |  |  |
| `CS.ackermann_total` | useful library result | chris | DOMAIN-cs | `5be55da9ff893ad1` | 2 |  |
| `CS.binary_search_correct` | useful library result | chris | DOMAIN-cs | `5819317f04d2c782` | 2 |  |
| `CS.cantor_powerset` | useful library result | admin | DOMAIN-cs | `05236d9786b6bf49` | 2 |  |
| `CS.dfa_complement_regular` | useful library result | admin | DOMAIN-cs | `5393eeda2aabde9f` | 2 |  |
| `CS.disjointness_lb` | routine formalization | chris | FRONTIER-cs | `27008beec724a6cd` |  |  |
| `CS.euclid_gcd_correct` | useful library result | admin | DOMAIN-cs | `5cd1433f771a52d5` | 2 |  |
| `CS.halting_undecidable` | useful library result | admin | DOMAIN-cs | `a7068a118c89e6a6` | 2 |  |
| `CS.insertion_sort_correct` | useful library result | admin | DOMAIN-cs | `ac1daf678dc6586f` | 2 |  |
| `CS.knaster_tarski` | useful library result | admin | DOMAIN-cs | `9be952f97cf4bf06` | 2 |  |
| `CS.master_theorem_case1` | useful library result | admin | DOMAIN-cs | `12a20a335a56a15f` | 2 |  |
| `CS.mergesort_correct` | useful library result | chris | DOMAIN-cs | `84705364d9e6da56` | 2 |  |
| `CS.pcp_pigeon_bound` | useful library result | admin | DOMAIN-cs | `b6f373d132aa244d` | 2 |  |
| `CS.pigeonhole_hash` | useful library result | chris | DOMAIN-cs | `439f5007a2116736` | 2 |  |
| `CS.recursion_theorem` | routine formalization | chris | FRONTIER-cs | `992b85b6f682ca82` |  |  |
| `CS.rice_extended` | routine formalization | admin | FRONTIER-cs | `0de346fe2e44efe8` |  |  |
| `CS.rice_nontrivial` | useful library result | chris | DOMAIN-cs | `70b0d5d3f3462bb2` | 2 |  |
| `CS.sorting_lb_3` | useful library result | admin | DOMAIN-cs | `3ae22cb6cd5d5634` | 2 |  |
| `CS.sorting_lb_5` | useful library result | admin | DOMAIN-cs | `927e6e8db806074d` | 2 |  |
| `CS.time_hierarchy` | routine formalization | chris | FRONTIER-cs | `5ce4563e6ac080b8` |  |  |
| `CS.yao_principle` | routine formalization | chris | FRONTIER-cs | `b5af82aa738ec12a` |  |  |
| `D5_card_verified` | routine formalization | chris | Brockian-external | `d2ba6c25a75509cf` |  | theorem is only \|D5\| = 10; file header overclaims an RH reduction |
| `Fibonacci.cassini` | routine formalization | admin | FRONTIER-fib | `12987c1ffdf5e546` |  |  |
| `Fibonacci.catalan` | routine formalization | admin | FRONTIER-fib | `6bd4c6bae16fa9d7` |  |  |
| `Fibonacci.consecutive_coprime` | routine formalization | chris | FRONTIER-fib | `8a84550ba1416f17` |  |  |
| `Fibonacci.divides` | routine formalization | chris | FRONTIER-fib | `346402062416ba32` |  |  |
| `Fibonacci.dOcagne` | routine formalization | admin | FRONTIER-fib | `2069642fe87bea2a` |  |  |
| `Fibonacci.gcd` | routine formalization | chris | FRONTIER-fib | `857f771ba5dc0183` |  |  |
| `Fibonacci.sum_first_n` | routine formalization | admin | FRONTIER-fib | `05aa23a900b82cde` |  |  |
| `Fibonacci.zeckendorf_small` | routine formalization | admin | FRONTIER-fib | `c31694fbf31cf7d6` |  |  |
| `Frontier.abc_statement` | routine formalization | admin | FRONTIER-primes | `eb4e9fc80e805d1c` |  | statement/definition only; headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.AlgebraLogic.lagrange` | routine formalization | chris | External | `7587715b0941897d` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.AnalysisCalculus.am_gm_two` | routine formalization | chris | External | `f7a198cedb7bc4fa` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.arrow_impossibility` | useful library result | chris | FRONTIER-mind | `3bba0a01f8f2fb58` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.artin_primitive_root` | routine formalization | chris | FRONTIER-primes | `1492e48d4cb47380` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.asymptotic_freedom_sign` | routine formalization | chris | FRONTIER-physics | `2f9475982f12ae07` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.atiyah_singer_index` | routine formalization | admin | FRONTIER-fields | `cfe09de54e53371c` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.bell_theorem` | routine formalization | chris | FRONTIER-physics | `6b73bd27e55f1b36` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.bhargava_cube_law` | routine formalization | chris | FRONTIER-fields | `9b5d5ec137bae5eb` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.Borel_determinacy` | routine formalization | chris | FRONTIER-set | `edb6b2fcd636e24a` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.bounded_prime_gaps` | routine formalization | chris | FRONTIER-primes | `6af14ac924df9f96` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.BrockianNextLevel.excluded_residue_count` | routine formalization | chris | Brockian-external | `bf1d825039c42bad` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.BrockianSieveDeep.nu_le_card` | routine formalization | chris | Brockian-external | `b91fed8195f95856` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.BSD_statement` | routine formalization | admin | FRONTIER-moonshot | `ed588c2a76b123ec` |  | statement/definition only; headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.Catalan_Mihailescu` | routine formalization | chris | FRONTIER-primes | `b6e79deae78b04e1` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.CH_independent_statement` | routine formalization | admin | FRONTIER-set | `201832127c4651e4` |  | statement/definition only; headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.CombinatoricsGraph.handshake` | routine formalization | chris | External | `d95e6547226821e1` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.CryptoComplexity.otp_bijective` | routine formalization | chris | External | `d2128dec6b9cbbb6` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.deligne_weil_RH` | routine formalization | chris | FRONTIER-fields | `3a3c2fbb7f48fcda` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.erdos_discrepancy` | routine formalization | chris | FRONTIER-primes | `770c33efcc2330de` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.faltings_mordell` | routine formalization | admin | FRONTIER-fields | `3eff515b5d75f756` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.feit_thompson_odd_order` | routine formalization | chris | FRONTIER-abel | `88772ba40e0dd4f2` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.five_color_theorem` | routine formalization | admin | FRONTIER-fields | `4818760c077e4cf0` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.FLT_statement` | routine formalization | admin | FRONTIER-primes | `4093fc01187cc2ac` |  | statement/definition only; headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.Gale_Stewart_open` | useful library result | chris | FRONTIER-set | `c2fc4afa4563f337` | 2 | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.gleason_theorem` | routine formalization | chris | FRONTIER-physics | `b6c8b531e717df87` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.global_workspace_fixpoint` | routine formalization | admin | FRONTIER-mind | `274d2f2675110f3a` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.Goedel_second_incompleteness` | routine formalization | admin | FRONTIER-set | `82e9c744dd2834e3` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.good_regulator` | routine formalization | admin | FRONTIER-mind | `59ae3c92dd361562` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.Goodstein_terminates` | routine formalization | admin | FRONTIER-set | `8dc1f28b5fe58da0` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.Green_Tao` | routine formalization | chris | FRONTIER-primes | `f9af0ea465291d63` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.higgs_mass_toy` | routine formalization | admin | FRONTIER-physics | `3a1b3fcc292bca78` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.huh_matroid_log_concave` | routine formalization | admin | FRONTIER-fields | `dc1479901a03e887` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.iit_phi_partition` | routine formalization | admin | FRONTIER-mind | `209a660b1083902e` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.infinite_ramsey` | routine formalization | chris | FRONTIER-set | `018304d11c863a4c` | 2 | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.InformationTheory.entropy_term_nonneg` | routine formalization | chris | External | `ef34fe5a60f3475b` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.kam_theorem` | routine formalization | admin | FRONTIER-physics | `60a1eb52899fbd08` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.kochen_specker` | useful library result | admin | FRONTIER-physics | `26ecc7856533d159` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.lindenstrauss_QUE` | routine formalization | admin | FRONTIER-fields | `a489e840093dc2b8` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.loeb_no_self_trust` | routine formalization | chris | FRONTIER-mind | `78813dec6cb44bb5` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.margulis_superrigidity` | routine formalization | chris | FRONTIER-abel | `93878f0e09b56e18` |  | headline theorem supplied as a premise; headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.mcmullen_renormalization` | routine formalization | admin | FRONTIER-fields | `8afadf4a5196580a` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.milnor_exotic_7sphere` | routine formalization | admin | FRONTIER-abel | `86516364af85afe3` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.Mordell_finite_generation` | routine formalization | admin | FRONTIER-primes | `005622ffaf77a7f8` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.no_communication` | useful library result | chris | FRONTIER-physics | `c03525002e84d5c5` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.noether_conservation` | useful library result | admin | FRONTIER-physics | `d001052f5c28ed4a` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.onsager_2d_ising` | routine formalization | chris | FRONTIER-physics | `838925db8c76e75b` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.P_vs_NP_statement` | routine formalization | admin | FRONTIER-moonshot | `32ebed60f5603cec` | 2 | statement/definition only; headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.PhysicsQM.pauli_sq_X` | routine formalization | chris | External | `209c19ffb0a69beb` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.poincare_3sphere` | routine formalization | admin | FRONTIER-moonshot | `34a73a9e501e35ab` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.RH_Li_criterion` | routine formalization | chris | FRONTIER-moonshot | `eb2711b719eec98a` | 2 | finite symmetric-zero model; not the classical infinite Li criterion; headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.RH_statement` | routine formalization | chris | FRONTIER-moonshot | `cd080a1240440439` |  | statement/definition only; headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.scholze_perfectoid_tilt` | useful library result | admin | FRONTIER-fields | `b5819e2a78b81d34` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.self_nonprediction` | routine formalization | admin | FRONTIER-mind | `b3b6e566c221120c` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.Sensitivity.flipAt_apply` | routine formalization | chris | External | `7faf57d2efdee1ad` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.smirnov_percolation` | routine formalization | chris | FRONTIER-fields | `7ddfae3e7b8b1bcd` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.Spectral.cycle_fiedler_value` | useful library result | chris | FRONTIER-spectral | `97ea25f89bfd5f34` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.Spectral.cycle_laplacian_spectrum` | useful library result | admin | FRONTIER-spectral | `31bfdea468d3b864` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.Spectral.gap_to_cancellation_conditional` | useful library result | chris | FRONTIER-spectral | `d5cd4add18a1be50` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.spin_statistics` | routine formalization | admin | FRONTIER-physics | `6a505d1c8c3f7694` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.ssh_winding_invariant` | routine formalization | chris | FRONTIER-physics | `110ad26144a7224c` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.sum_three_cubes_42` | routine formalization | admin | FRONTIER-primes | `3a997b7b35b33604` | 2 | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.Suslin_line` | routine formalization | admin | FRONTIER-set | `4a1bbabf0e07a332` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.Tarski_undefinability` | useful library result | admin | FRONTIER-set | `8fb4fd2f132f721a` | 2 | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.thurston_geometrization` | routine formalization | admin | FRONTIER-fields | `6e4da8d9fb6e1d23` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.tknn_chern_hall` | useful library result | admin | FRONTIER-physics | `346b7ce3d811811f` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Frontier.wigderson_expander_mixing` | routine formalization | admin | FRONTIER-abel | `dca1fb1528fb4bd2` |  | headline namespace; inspect exact statement before repeating the name as a claim |
| `Goldbach.conjecture_statement` | routine formalization | admin | FRONTIER-primes | `eff6632fbe3cfe33` |  | statement/definition only |
| `Goldbach.instance_100` | routine formalization | admin | FRONTIER-primes | `2d650bae9a27b01a` |  |  |
| `Goldbach.instance_1000` | routine formalization | chris | FRONTIER-primes | `85513e5cd58d0820` |  |  |
| `Goldbach.ternary_statement` | routine formalization | admin | FRONTIER-primes | `f8425159e028644c` |  | statement/definition only |
| `goldbachReps_nonneg` | routine formalization | chris | External | `1302921d11377ebb` |  |  |
| `GoldbachSpectral.reps_positive_implies_goldbach` | routine formalization | chris | External | `2a0f7a2ccc288afc` |  |  |
| `GroupTheory.cauchy` | routine formalization | chris | FRONTIER-wave2 | `f560dc1b68fb05bd` |  |  |
| `GroupTheory.lagrange` | routine formalization | admin | FRONTIER-wave2 | `8e7223d3c1b71633` |  |  |
| `idemp_implies_double_idemp` | routine formalization | admin | External | `a0344b63996061a6` |  |  |
| `imp_A1` | routine formalization | admin | External | `e96115d400050eb1` |  |  |
| `Infinity.aleph0_add_aleph0` | routine formalization | chris | FRONTIER-set | `ce453b8318bdd5a2` |  |  |
| `Infinity.cantor_no_injection_from_powerset` | routine formalization | admin | FRONTIER-set | `4a83afeb42a8efe4` |  |  |
| `Infinity.cantor_no_surjection` | routine formalization | chris | FRONTIER-set | `b48657174ca186c1` |  |  |
| `Infinity.cardinal_lt_power` | routine formalization | admin | FRONTIER-set | `e84245c0057554f0` |  |  |
| `Infinity.countable_nat` | routine formalization | chris | External | `50f2b2b88801a036` |  |  |
| `Infinity.konig_lt` | routine formalization | admin | FRONTIER-set | `611769db3e374339` |  |  |
| `Infinity.nat_countable` | routine formalization | admin | FRONTIER-set | `63654bd1592bc6ca` |  |  |
| `Infinity.rationals_countable` | routine formalization | admin | FRONTIER-set | `00d33e3256849770` |  |  |
| `Infinity.reals_uncountable` | routine formalization | admin | FRONTIER-set | `8e1ca6f09273aea0` |  |  |
| `Infinity.schroeder_bernstein` | routine formalization | chris | FRONTIER-set | `f20b532e064b192b` |  |  |
| `LargeCardinal.inaccessible_statement` | routine formalization | chris | FRONTIER-wave2 | `566437bf3df74676` |  | statement/definition only |
| `LargeCardinal.measurable_statement` | routine formalization | chris | FRONTIER-wave2 | `d2be20f5c2f828ea` |  | statement/definition only |
| `left_proj_imp_idem` | routine formalization | admin | External | `4e87053fcfb1587c` |  |  |
| `LinearRecurrence.casoratian_step` | routine formalization | chris | External | `52104dc73d6f8c71` |  |  |
| `Math.baire_category` | routine formalization | chris | DOMAIN-math | `4592eefe59b5a399` | 2 |  |
| `Math.bertrand_postulate` | routine formalization | admin | DOMAIN-math | `76bf222bbcb6525e` | 2 |  |
| `Math.bolzano_weierstrass` | routine formalization | admin | DOMAIN-math | `894067bb0fa0f9b7` | 2 |  |
| `Math.cassini_10` | routine formalization | admin | DOMAIN-math | `8049b8ae3b18535e` | 2 |  |
| `Math.cassini_11` | routine formalization | admin | DOMAIN-math | `d7c6806127398ed5` | 2 |  |
| `Math.cassini_12` | routine formalization | admin | DOMAIN-math | `eacb154d02bc7e1c` | 2 |  |
| `Math.cassini_13` | routine formalization | admin | DOMAIN-math | `a31d3878e61b0051` | 2 |  |
| `Math.cassini_14` | routine formalization | admin | DOMAIN-math | `21b54ab7e5f79660` | 2 |  |
| `Math.cassini_15` | routine formalization | admin | DOMAIN-math | `5ddecdb7fefe7eb1` | 2 |  |
| `Math.cassini_2` | routine formalization | admin | DOMAIN-math | `9fd5e560a8db5318` | 2 |  |
| `Math.cassini_3` | routine formalization | chris | DOMAIN-math | `05cf7dc1794329c6` | 2 |  |
| `Math.cassini_4` | routine formalization | chris | DOMAIN-math | `8577f6af0b7e805c` | 2 |  |
| `Math.cassini_5` | routine formalization | admin | DOMAIN-math | `b6473aedc40dde72` | 2 |  |
| `Math.cassini_6` | routine formalization | admin | DOMAIN-math | `fec96477afdda0ae` | 2 |  |
| `Math.cassini_7` | routine formalization | admin | DOMAIN-math | `3f57f1f2a0b38aed` | 2 |  |
| `Math.cassini_8` | routine formalization | admin | DOMAIN-math | `508d785592ba4329` | 2 |  |
| `Math.cassini_9` | routine formalization | admin | DOMAIN-math | `b5001dc75910df2d` | 2 |  |
| `Math.catalan_closed` | routine formalization | admin | DOMAIN-math | `b94e81dfec404f85` | 2 |  |
| `Math.cauchy_group` | routine formalization | chris | DOMAIN-math | `aa49ea1f0a249a9c` | 2 |  |
| `Math.chinese_remainder` | routine formalization | chris | DOMAIN-math | `25c2872190531e32` | 2 |  |
| `Math.dilworth` | routine formalization | admin | DOMAIN-math | `e9cae54ddbaf00e1` | 2 |  |
| `Math.fermat_little` | routine formalization | chris | DOMAIN-math | `9d9e003c1778cf53` | 2 |  |
| `Math.fta_algebra` | routine formalization | admin | DOMAIN-math | `d6f47bbac040e695` | 2 |  |
| `Math.heine_borel` | routine formalization | admin | DOMAIN-math | `5871efa2dfbf937b` | 2 |  |
| `Math.inclusion_exclusion` | routine formalization | chris | DOMAIN-math | `7eb1d983467ae52c` | 2 |  |
| `Math.ivt` | routine formalization | chris | DOMAIN-math | `f2c201e16e5da12e` | 2 |  |
| `Math.lagrange_four_squares` | routine formalization | admin | DOMAIN-math | `de092cd3fc078ed3` | 2 |  |
| `Math.lagrange_subgroup` | routine formalization | admin | DOMAIN-math | `8d34f2ba0ce9b425` | 2 |  |
| `Math.mean_value` | routine formalization | admin | DOMAIN-math | `f86a967c44c78a28` | 2 |  |
| `Math.mobius_root_sum_1` | routine formalization | admin | DOMAIN-math | `af4050c49a83554e` |  |  |
| `Math.mobius_root_sum_10` | routine formalization | admin | DOMAIN-math | `9912a3d35ece8073` |  |  |
| `Math.mobius_root_sum_11` | routine formalization | admin | DOMAIN-math | `5e29083fc97f4b44` |  |  |
| `Math.mobius_root_sum_12` | routine formalization | admin | DOMAIN-math | `6a1a681c84a20c73` |  |  |
| `Math.mobius_root_sum_2` | routine formalization | admin | DOMAIN-math | `cb969c147d2f7427` |  |  |
| `Math.mobius_root_sum_3` | routine formalization | admin | DOMAIN-math | `e8a118054ff09fbc` |  |  |
| `Math.mobius_root_sum_4` | routine formalization | admin | DOMAIN-math | `457528fc526c893c` |  |  |
| `Math.mobius_root_sum_5` | routine formalization | admin | DOMAIN-math | `1cec11f58dba4624` |  |  |
| `Math.mobius_root_sum_6` | routine formalization | chris | DOMAIN-math | `7f18877409d1a564` |  |  |
| `Math.mobius_root_sum_7` | routine formalization | chris | DOMAIN-math | `3b642dad2514ab0e` |  |  |
| `Math.mobius_root_sum_8` | routine formalization | chris | DOMAIN-math | `1453b26c807a08fd` |  |  |
| `Math.mobius_root_sum_9` | routine formalization | chris | DOMAIN-math | `42d0c2ef3bb4e64d` |  |  |
| `Math.pell_10` | routine formalization | admin | DOMAIN-math | `ccbe7ca4d99d37a9` |  |  |
| `Math.pell_11` | routine formalization | admin | DOMAIN-math | `8aec043e4fd559ba` |  |  |
| `Math.pell_13` | routine formalization | admin | DOMAIN-math | `d0a5c23030b69325` |  |  |
| `Math.pell_2` | routine formalization | admin | DOMAIN-math | `fa761ee0a83c2ead` |  |  |
| `Math.pell_3` | routine formalization | admin | DOMAIN-math | `891cd395b99c80d5` |  |  |
| `Math.pell_5` | routine formalization | admin | DOMAIN-math | `3ad0a9402dc50ed1` |  |  |
| `Math.pell_6` | routine formalization | chris | DOMAIN-math | `6e6d97b644483c5e` |  |  |
| `Math.pell_7` | routine formalization | chris | DOMAIN-math | `d353a69fe262f1d2` |  |  |
| `Math.pell_8` | routine formalization | admin | DOMAIN-math | `031a7217b98d510b` |  |  |
| `Math.quadratic_reciprocity` | routine formalization | admin | DOMAIN-math | `2721b6da290a88b0` | 2 |  |
| `Math.ramsey_3_3` | routine formalization | chris | DOMAIN-math | `0b31aa4506ddc017` | 2 |  |
| `Math.sum_two_squares` | routine formalization | admin | DOMAIN-math | `e6522493ae3635b4` | 2 |  |
| `Math.two_squares_101` | routine formalization | chris | DOMAIN-math | `3c190498ed6afed7` | 2 |  |
| `Math.two_squares_109` | routine formalization | admin | DOMAIN-math | `bde1be57f83152c4` | 2 |  |
| `Math.two_squares_113` | routine formalization | chris | DOMAIN-math | `7ffd16d3dec52a12` | 2 |  |
| `Math.two_squares_13` | routine formalization | admin | DOMAIN-math | `276063bd7f4ad041` | 2 |  |
| `Math.two_squares_17` | routine formalization | admin | DOMAIN-math | `b7ebfa95c76f3b50` | 2 |  |
| `Math.two_squares_29` | routine formalization | admin | DOMAIN-math | `93630aa7995ad1f8` | 2 |  |
| `Math.two_squares_37` | routine formalization | admin | DOMAIN-math | `628a8d71f5607ec2` | 2 |  |
| `Math.two_squares_41` | routine formalization | admin | DOMAIN-math | `1456a0fe621a01bb` | 2 |  |
| `Math.two_squares_5` | routine formalization | chris | DOMAIN-math | `779705fdf985e56f` | 2 |  |
| `Math.two_squares_53` | routine formalization | admin | DOMAIN-math | `09ee78019f79bf99` | 2 |  |
| `Math.two_squares_61` | routine formalization | chris | DOMAIN-math | `d283e293dc22f279` | 2 |  |
| `Math.two_squares_73` | routine formalization | admin | DOMAIN-math | `d9147b075b953191` | 2 |  |
| `Math.two_squares_89` | routine formalization | admin | DOMAIN-math | `21453875e5747468` | 2 |  |
| `Math.two_squares_97` | routine formalization | admin | DOMAIN-math | `5c98c3b0776a2392` | 2 |  |
| `Math.weierstrass_approx` | routine formalization | admin | DOMAIN-math | `5d0e018c31ccb65e` | 2 |  |
| `Math.wilson_theorem` | routine formalization | admin | DOMAIN-math | `06afb7b7430d7619` | 2 |  |
| `Math2.erdos_ko_rado` | routine formalization | chris | FRONTIER-math | `91ecc58c6639b86a` |  |  |
| `Math2.kruskal_katona` | routine formalization | chris | FRONTIER-math | `1ace123608cefe7a` |  |  |
| `Math2.van_der_waerden` | routine formalization | chris | FRONTIER-math | `84a7df67b1b1d859` |  |  |
| `Mod5Ray.card` | routine formalization | chris | External | `985b54079e882cdb` |  |  |
| `MS.Algebra.lagrange_subgroup` | routine formalization | admin | External | `bd0d8c8371c9c86a` |  |  |
| `MS.Analysis.intermediate_value` | routine formalization | chris | External | `860b61ff40cca0dd` |  |  |
| `MS.Brockian.universal_admissibility_count` | routine formalization | admin | Brockian-external | `17c9534a321723df` |  |  |
| `MS.Combinatorics.ramsey_finite` | routine formalization | admin | External | `c1a944364e54d8a2` |  |  |
| `MS.Foundations.fundamental_theorem_of_algebra` | routine formalization | chris | External | `5d95404e76ae4b4d` |  |  |
| `MS.LogicQuantum.schroeder_bernstein` | routine formalization | admin | External | `9a57bf0ae4f57211` |  |  |
| `MS2.Algebra2.orbit_stabilizer` | routine formalization | chris | External | `d600bbfe98bc8eb6` |  |  |
| `MS2.Analysis2.squeeze` | routine formalization | chris | External | `d3a0581773b9ac6b` |  |  |
| `MS2.BSpec2.P6_eigen_center` | routine formalization | chris | Brockian-external | `98763909f398495e` |  |  |
| `MS2.CSLogic.cantor_diagonal` | routine formalization | chris | External | `26d70ae6bb34c2c3` |  |  |
| `MS2.FibLucas.cassini` | routine formalization | chris | External | `ef632fb8bb864af5` |  |  |
| `MS2.Geometry.law_of_cosines` | routine formalization | chris | External | `69b267be56416998` |  |  |
| `MS2.IT2.entropy_nonneg` | routine formalization | chris | External | `4e3d8a5c13546323` |  |  |
| `MS2.NT2.chinese_remainder` | routine formalization | chris | External | `bb09dd07a9482540` |  |  |
| `MS2.Prob2.am_gm_three` | routine formalization | chris | External | `b787d80661891533` |  |  |
| `MS2.Probability.markov_finite` | routine formalization | chris | External | `8f8e6164f5177d31` |  |  |
| `MS2.QI3.cnot_involutive` | routine formalization | chris | External | `8a78773bbf1af5b3` |  |  |
| `NumberTheory.euler_totient` | routine formalization | admin | FRONTIER-wave2 | `68ee247fc2ba37fe` |  |  |
| `NumberTheory.fermat_little` | routine formalization | admin | FRONTIER-wave2 | `13a2d6f81e380920` |  |  |
| `NumberTheory.infinitude_primes_4k3` | routine formalization | admin | FRONTIER-wave2 | `792515ed578ef28b` |  |  |
| `NumberTheory.quadratic_reciprocity` | routine formalization | admin | FRONTIER-wave2 | `8ab339a208a0f879` |  |  |
| `NumberTheory.wilson` | routine formalization | chris | FRONTIER-wave2 | `4fb1bc519b66e7ae` |  |  |
| `NymanBeurling.finite_distance_nonneg` | routine formalization | chris | FRONTIER-wave2 | `364abb1761842c07` |  |  |
| `Ordinal.epsilon0_fixed_point` | routine formalization | admin | FRONTIER-wave2 | `648e858f0ca85f0a` |  |  |
| `Ordinal.natCast_add` | routine formalization | admin | FRONTIER-wave2 | `de5ea9470eb1c28a` |  |  |
| `Ordinal.omega_add_omega` | routine formalization | chris | FRONTIER-wave2 | `6e93ff58ac26cdda` |  |  |
| `Ordinal.omega_le_omega_pow` | routine formalization | admin | FRONTIER-wave2 | `973b22ec02af2aea` |  |  |
| `pairs_always_q_minus_2` | routine formalization | chris | External | `b2fec5c8da04d1dd` |  |  |
| `pattern_reflection_invariance` | routine formalization | chris | External | `b9c7ddaa99762ae5` |  |  |
| `PCA.Cert.ed25519_verify_sound` | useful library result | admin | D-pca-meta | `caf0ece41a7efb8b` | 2 |  |
| `PCA.Cert.reprove_matches_iff_untampered` | useful library result | admin | D-pca-meta | `a62955ab380544d6` | 2 |  |
| `PCA.Coverage.bail_on_unrecognized_is_sound` | useful library result | chris | D-pca-meta | `bc392adff8a9e6e6` | 2 |  |
| `PCA.default_deny` | useful library result | chris | PCA-lean | `f59eaadabbb4ddaf` | 2 |  |
| `PCA.escape_monotone` | useful library result | admin | PCA-lean | `504714607f29640c` | 2 |  |
| `PCA.Fix.alter_policy_preserves_roles_and_cmd` | useful library result | admin | D-pca-meta | `944143ee58263919` | 2 |  |
| `PCA.Invariant.default_deny_excludes_only_allowlist` | useful library result | admin | D-pca-meta | `935a162d0002d811` | 2 |  |
| `PCA.Invariant.rls_off_implies_no_row_protection` | useful library result | chris | D-pca-meta | `6b7fc14c7501ec3b` | 2 |  |
| `PCA.Isolation.disjunction_split_preserves_semantics` | useful library result | admin | D-pca-meta | `66840caa1f5599a5` | 2 |  |
| `PCA.Isolation.evalF_bigOr` | useful library result | admin | External | `c24e0bbc4b79230a` |  |  |
| `PCA.Isolation.in_scope_encoding_complete` | useful library result | chris | D-pca-meta | `af022fb135f07d07` | 2 |  |
| `PCA.Isolation.in_scope_encoding_sound` | useful library result | chris | D-pca-meta | `b42688d348939086` | 2 |  |
| `PCA.Isolation.no_clean_proved_with_escape` | useful library result | admin | D-pca-meta | `6253964c8582619f` | 2 |  |
| `PCA.Isolation.null_escape_iff_unowned_reachable` | useful library result | admin | D-pca-meta | `208528aadab691fa` | 2 |  |
| `PCA.Isolation.tightened_predicate_refines_original` | useful library result | chris | D-pca-meta | `dabf2be829d9b3cf` | 2 |  |
| `PCA.leak_iff_escape_when_out_of_scope` | useful library result | chris | PCA-lean | `d7edfec0f486f88a` | 2 |  |
| `PCA.no_clean_proved_with_escape` | useful library result | admin | PCA-lean | `5da1f2207d51a4b7` | 2 |  |
| `PCA.no_escape_no_leak` | useful library result | chris | PCA-lean | `1823e80fd0c3e702` | 2 |  |
| `PCA.owner_only_isolated` | useful library result | admin | PCA-lean | `a21e663523cf6992` | 2 |  |
| `PCA.priv_is_escape` | useful library result | admin | PCA-lean | `d34e39b2e6be5e07` | 2 |  |
| `PCA.tightening_refines` | useful library result | admin | PCA-lean | `7977cd0dd33e11db` | 2 |  |
| `PCA.unowned_is_hole` | useful library result | chris | PCA-lean | `382c94122396eef3` | 2 |  |
| `PCA.with_check_true_admits_forge` | useful library result | admin | PCA-lean | `688f3f98ff6c7343` | 2 |  |
| `PCA.WriteIntegrity.member_check_prevents_cross_tenant_write` | useful library result | admin | D-pca-meta | `e30ef383ef118089` | 2 |  |
| `PCA.WriteIntegrity.with_check_true_admits_forge` | useful library result | chris | D-pca-meta | `633c3463383c516b` | 2 |  |
| `Phenomenology.mereology_partialorder` | routine formalization | chris | FRONTIER-set | `a280c055485fcfa3` |  |  |
| `phi_pos` | routine formalization | chris | External | `96e666d7bf4bfcc1` |  |  |
| `Phys.bekenstein_bound` | routine formalization | chris | FRONTIER-phys | `154d941ec7295f40` |  |  |
| `Phys.bloch_theorem` | routine formalization | admin | FRONTIER-phys | `ac457098aa0d7162` |  |  |
| `Phys.crooks_theorem` | routine formalization | admin | FRONTIER-phys | `4034ffed0e927622` |  |  |
| `Phys.hawking_temperature` | routine formalization | admin | FRONTIER-phys | `9973baedddbdf069` |  |  |
| `Phys.jarzynski_equality` | routine formalization | chris | FRONTIER-phys | `02ba8c46702f7d67` |  |  |
| `Phys.kochen_specker_18` | useful library result | admin | FRONTIER-phys | `d720a445fd22066c` |  |  |
| `Phys.kramers_degeneracy` | routine formalization | chris | FRONTIER-phys | `a812150d666bb08d` |  |  |
| `Phys.landauer_principle` | routine formalization | admin | FRONTIER-phys | `a1a05ace95533f3a` |  |  |
| `Phys.unruh_effect` | routine formalization | admin | FRONTIER-phys | `4ad17ebbc89d4797` |  |  |
| `Phys.wigner_eckart` | routine formalization | chris | FRONTIER-phys | `aaa81c5358d95c9a` |  |  |
| `PrimeAdmissibility.universal_admissibility_count` | routine formalization | chris | External | `6e320e67cfae6e59` |  |  |
| `Primes.bertrand` | routine formalization | admin | FRONTIER-primes | `00e65a4c7ab14b70` |  |  |
| `Primes.infinitude` | routine formalization | chris | FRONTIER-primes | `1aa17c5e48de597c` |  |  |
| `Primes.reciprocal_sum_diverges` | routine formalization | admin | FRONTIER-primes | `12181f11bd610ac8` |  |  |
| `problem_normal_0166` | routine formalization | admin | External | `92f2cf7fd37b2cf8` |  |  |
| `problem_normal_0355` | routine formalization | admin | External | `75b1017d29e3143e` |  |  |
| `problem_normal_0765` | routine formalization | admin | External | `618ce51e1c190c71` |  |  |
| `ProvabilityStructure.imp_self_thm` | routine formalization | chris | External | `72a8cd741abb5c7c` |  |  |
| `QC.bell_orthonormal` | useful library result | admin | DOMAIN-qc | `8bea6a6c56a697da` | 1 |  |
| `QC.bloch_sphere_bijection` | useful library result | chris | DOMAIN-qc | `b3a97931bd4c67ca` | 1 |  |
| `QC.chsh_tsirelson` | useful library result | chris | DOMAIN-qc | `7ec2bd810c298729` | 1 |  |
| `QC.cnot_unitary_involutive` | useful library result | admin | DOMAIN-qc | `97de5ae71ea79ac9` | 1 |  |
| `QC.density_matrix_unitary_invariant` | useful library result | chris | DOMAIN-qc | `6f31a666de77b65b` | 1 |  |
| `QC.deutsch_correct` | useful library result | admin | DOMAIN-qc | `453fc1c83a7427be` | 1 |  |
| `QC.exists_norm_eq_one` | useful library result | admin | External | `59d59b51afaf7760` |  |  |
| `QC.ghz_nonlocal` | useful library result | chris | DOMAIN-qc | `181ac2b542fec7af` | 1 |  |
| `QC.ghz2_normalized` | routine formalization | admin | DOMAIN-qc | `11f7c0017ae5cd22` | 1 |  |
| `QC.ghz3_normalized` | routine formalization | admin | DOMAIN-qc | `9961dcc135346455` | 1 |  |
| `QC.ghz4_normalized` | routine formalization | admin | DOMAIN-qc | `432af6bc06344686` | 1 |  |
| `QC.ghz5_normalized` | routine formalization | admin | DOMAIN-qc | `de8a28c374931945` | 1 |  |
| `QC.ghz6_normalized` | routine formalization | admin | DOMAIN-qc | `ca44676e6e5dd925` | 1 |  |
| `QC.ghz7_normalized` | routine formalization | admin | DOMAIN-qc | `858a3d22211c9dff` | 1 |  |
| `QC.ghz8_normalized` | routine formalization | admin | DOMAIN-qc | `35fbdefe36771196` | 1 |  |
| `QC.hadamard_involutive` | useful library result | admin | DOMAIN-qc | `2feabe10bdf44d14` | 1 |  |
| `QC.hadamard_XZ` | useful library result | admin | DOMAIN-qc | `9c1c46256a294d67` | 1 |  |
| `QC.kraus_trace_preserving` | useful library result | chris | DOMAIN-qc | `d57abce96b02db84` | 1 |  |
| `QC.no_cloning` | useful library result | admin | DOMAIN-qc | `1dd99dc198e8dcd0` | 1 |  |
| `QC.pauli_anticommute` | useful library result | admin | DOMAIN-qc | `156e43685efbea3d` | 1 |  |
| `QC.pauli_basis` | useful library result | admin | DOMAIN-qc | `219ad1153eb47d1d` | 1 |  |
| `QC.pure_state_zero_entropy` | useful library result | admin | DOMAIN-qc | `fc7eede073165729` | 1 |  |
| `QC.qft_unitary` | useful library result | admin | DOMAIN-qc | `900f5ec846a1d682` | 1 |  |
| `QC.qft_unitary_2` | routine formalization | chris | DOMAIN-qc | `b8868fa83c344e4b` | 1 |  |
| `QC.qft_unitary_3` | routine formalization | admin | DOMAIN-qc | `a5ee18c536c06c0e` | 1 |  |
| `QC.qft_unitary_4` | routine formalization | chris | DOMAIN-qc | `8be0569c0b1aa37b` | 1 |  |
| `QC.qft_unitary_5` | routine formalization | admin | DOMAIN-qc | `dc97f35c4d0fcd98` | 1 |  |
| `QC.qft_unitary_6` | routine formalization | chris | DOMAIN-qc | `96e926d170198471` | 1 |  |
| `QC.qft_unitary_7` | routine formalization | admin | DOMAIN-qc | `c397a1f90f3f8c98` | 1 |  |
| `QC.qft_unitary_8` | routine formalization | chris | DOMAIN-qc | `92ee7e14499fea89` | 1 |  |
| `QC.robertson_uncertainty` | useful library result | chris | DOMAIN-qc | `c28d8fbe21f868dc` | 1 |  |
| `QC.superdense_two_bits` | useful library result | chris | DOMAIN-qc | `ea0eefa18683ab82` | 1 |  |
| `QC.swap_test_overlap` | useful library result | admin | DOMAIN-qc | `849378e48fa624d2` | 1 |  |
| `QC.teleportation_identity` | useful library result | chris | DOMAIN-qc | `bd5e5adcbba1b7bc` | 1 |  |
| `QC.tens_add_left` | useful library result | chris | External | `44a43ea545c43788` |  |  |
| `QC.toffoli_unitary` | useful library result | admin | DOMAIN-qc | `d4f595bb24698aaf` | 1 |  |
| `QI.apply_entry_eq_sum` | useful library result | admin | External | `b71c4d10ea721707` |  |  |
| `QI.choi_jamiolkowski` | useful library result | admin | FRONTIER-qi | `7960bca308bb5e86` |  |  |
| `QI.deutsch_jozsa` | useful library result | admin | FRONTIER-qi | `29d77aea2589a781` |  |  |
| `QI.inner_kron` | useful library result | chris | External | `8a70be7c23b08592` |  |  |
| `QI.inner_tens_tens` | useful library result | admin | External | `4007c6a5fe3e8ae1` |  |  |
| `QI.inner_toVec` | useful library result | chris | External | `97072a2622745216` |  |  |
| `QI.knill_laflamme` | useful library result | admin | FRONTIER-qi | `70d81ff5f73689ad` |  |  |
| `QI.no_deleting` | useful library result | admin | FRONTIER-qi | `4e9054f64dda381a` |  |  |
| `QI.ptrace_pureProj` | useful library result | admin | External | `0b281fca8e3536f0` |  |  |
| `QI.ptraceSnd_outer` | useful library result | chris | External | `8ac49213df8e68d2` |  |  |
| `QI.purification_exists` | useful library result | chris | FRONTIER-qi | `f18bea87fd0db35c` |  |  |
| `QI.quantum_singleton` | useful library result | admin | FRONTIER-qi | `ca56a7cd39db65a4` |  |  |
| `QI.rho_apply` | useful library result | chris | External | `3b3e32b21ee1a201` |  |  |
| `QI.schmidt_decomposition` | useful library result | admin | FRONTIER-qi | `4c18927e965c101a` |  |  |
| `QI.shor_code_corrects` | useful library result | admin | FRONTIER-qi | `43ad187575fb3a85` |  |  |
| `QI.ten3_ofLp` | useful library result | chris | External | `9d4e4765be8773c8` |  |  |
| `QI.uhlmann_fidelity` | useful library result | admin | FRONTIER-qi | `50ca43727129e093` |  |  |
| `QPhys.box_level_1` | routine formalization | chris | DOMAIN-qphys | `df922485316612b8` |  |  |
| `QPhys.box_level_2` | routine formalization | admin | DOMAIN-qphys | `69ef6a65389d1a3a` |  |  |
| `QPhys.box_level_3` | routine formalization | admin | DOMAIN-qphys | `4bc6720c8d472b77` |  |  |
| `QPhys.box_level_4` | routine formalization | admin | DOMAIN-qphys | `faa399f3d5448a97` |  |  |
| `QPhys.box_level_5` | routine formalization | admin | DOMAIN-qphys | `014a528708cbfd15` |  |  |
| `QPhys.box_level_6` | routine formalization | chris | DOMAIN-qphys | `48eaed39cb6a3440` |  |  |
| `QPhys.box_level_7` | routine formalization | admin | DOMAIN-qphys | `6afc17fecb121c1e` |  |  |
| `QPhys.dLdq_eq_zero_of_translationInvariant` | useful library result | chris | External | `0d4c452a7dfabcb7` |  |  |
| `QPhys.heisenberg_uncertainty` | useful library result | chris | DOMAIN-qphys | `328f2130f383d15a` | 2 |  |
| `QPhys.hermitian_real_spectrum` | useful library result | admin | DOMAIN-qphys | `e4e3635028d5b0b8` | 2 |  |
| `QPhys.noether_translation` | useful library result | admin | DOMAIN-qphys | `84c68a34bd14ae09` | 2 |  |
| `QPhys.parseval_fourier` | useful library result | chris | DOMAIN-qphys | `8019d680a9511b73` | 2 |  |
| `QPhys.pauli_exclusion_antisym` | useful library result | admin | DOMAIN-qphys | `3ae668d019b71a8c` | 2 |  |
| `QPhys.unitary_time_evolution` | useful library result | chris | DOMAIN-qphys | `413500a4878fa472` | 2 |  |
| `QPhys.variational_bound` | useful library result | chris | DOMAIN-qphys | `3af6d8be7df33346` | 2 |  |
| `QuantumInfoII.clifford_HXH` | routine formalization | chris | External | `71ac8a7963ae7523` |  |  |
| `Riemann.BaezDuarte.distance_nonneg` | routine formalization | chris | FRONTIER-riemann | `fd528c69c1bdcc07` |  |  |
| `Riemann.BaezDuarte.gram_nonneg` | routine formalization | admin | FRONTIER-wave2 | `219a3ff06816e37e` |  |  |
| `Riemann.Chebyshev.psi_shadow` | routine formalization | admin | FRONTIER-riemann | `06aef012460d83f8` |  |  |
| `Riemann.CompletedZeta.functional_equation` | routine formalization | chris | FRONTIER-riemann | `2c36f160941ac92e` |  |  |
| `Riemann.functional.completed_symmetry_half` | routine formalization | admin | FRONTIER-riemann | `c0de49abac129800` |  |  |
| `Riemann.HardyZ.gram_positivity_3` | routine formalization | chris | FRONTIER-riemann | `72c02b4a1420b31f` |  |  |
| `Riemann.Li.lambda1_positive` | routine formalization | chris | FRONTIER-riemann | `6d43213f3f3393a0` |  |  |
| `Riemann.Li.lambda2_positive` | routine formalization | chris | FRONTIER-riemann | `07f3c1088922776f` |  |  |
| `Riemann.Li.lambda3_positive` | routine formalization | admin | FRONTIER-wave2 | `9da3023e2c6b6928` |  |  |
| `Riemann.Mertens.value_at_ten` | routine formalization | admin | FRONTIER-riemann | `d8a1cb2a1bcc540d` |  |  |
| `Riemann.Method.integrality_three_halves` | routine formalization | chris | FRONTIER-riemann | `83c44269bd8224f2` |  |  |
| `Riemann.method.rank_trace_c_general` | routine formalization | chris | FRONTIER-riemann | `2b47d2ce534ad2eb` |  |  |
| `Riemann.Method.rank_trace_c3_shadow` | routine formalization | admin | FRONTIER-wave2 | `ef0ea28459715f0a` |  |  |
| `Riemann.Method.simple_zero_shadow` | routine formalization | chris | FRONTIER-riemann | `e2e1443b15b9f1f0` |  |  |
| `Riemann.Nicolas.primorial_phi_shadow` | routine formalization | admin | FRONTIER-riemann | `186817df2bad23ce` |  |  |
| `Riemann.Redheffer.det_eq_mertens_3` | routine formalization | chris | FRONTIER-wave2 | `3fbb7b19f4219e89` |  |  |
| `Riemann.Redheffer.det_eq_mertens_4` | routine formalization | admin | FRONTIER-wave2 | `65f2c3f8e040e656` |  |  |
| `Riemann.Redheffer.det_eq_mertens_5` | routine formalization | admin | FRONTIER-wave2 | `19435ef7f3625731` |  |  |
| `Riemann.Redheffer.det_eq_mertens_6` | routine formalization | chris | FRONTIER-wave2 | `b5c497fe19813c53` |  |  |
| `Riemann.Robin.exceeds_bound_at_5040` | routine formalization | chris | FRONTIER-riemann | `03f64d26da5c9267` |  |  |
| `Riemann.Robin.sigma_5040` | routine formalization | admin | FRONTIER-riemann | `bfa9d298b1f51ac3` |  |  |
| `Riemann.Robin.sigma_one_sixteen` | routine formalization | chris | External | `8b0341e26eeca81e` |  |  |
| `Riemann.Weil.gram5_nonneg` | routine formalization | admin | FRONTIER-wave2 | `e4a49adfc00ce67f` |  |  |
| `Riemann.WeilPositivity.test_pair_nonneg` | routine formalization | chris | FRONTIER-riemann | `0fababb46f72330f` |  |  |
| `Riemann.zeta.euler_product_term_ne_zero` | routine formalization | chris | FRONTIER-riemann | `2253580fa330e163` |  |  |
| `Riemann.zeta.ne_zero_re_gt_one` | routine formalization | admin | FRONTIER-riemann | `2448a1fbc1079198` |  |  |
| `Riemann.Zeta.trivial_zero_neg_two` | routine formalization | admin | FRONTIER-riemann | `b8b6be492050bef3` |  |  |
| `Riemann.Zeta.value_at_two` | routine formalization | admin | FRONTIER-riemann | `e46c6e59efa46fa3` |  |  |
| `Riemann.Zeta.value_at_zero` | routine formalization | admin | FRONTIER-riemann | `5bebea815ba0b893` |  |  |
| `SetTheory.wellordering` | routine formalization | admin | FRONTIER-wave2 | `3831b53eece92449` |  |  |
| `SetTheory.zorn` | routine formalization | chris | FRONTIER-wave2 | `b0c3c67812625bd2` |  |  |
| `spiral_continuous` | routine formalization | chris | Brockian-external | `a6e9be5281354a8f` |  |  |
| `square_free_and_ne_one_implies_not_square` | routine formalization | chris | External | `87f144824c85e990` |  |  |
| `Topology.heine_borel_interval` | routine formalization | admin | FRONTIER-wave2 | `114fef2f847af9b6` |  |  |
| `Twin.conjecture_statement` | routine formalization | chris | FRONTIER-primes | `62f6422fdc90ef82` |  | statement/definition only |
| `Twin.pair_10007_10009` | routine formalization | chris | FRONTIER-primes | `7fdb0e7b568f42e3` |  |  |
| `Twin.pair_11_13` | routine formalization | admin | FRONTIER-primes | `89ad9be215dbf361` |  |  |
| `universal_count_theorem` | routine formalization | chris | External | `92393edd6d4a56ff` |  |  |
| `Zeta23Core.posIndex_conj_le` | useful library result | chris | C-corpus-extension | `7fdda1fc33bef775` |  |  |
| `Zeta23Core.rank_trace_ineq` | useful library result | chris | C-corpus-extension | `58f6eba66414bc93` |  |  |
| `Zeta23Core.sylvester_finrank_le_posIndex` | useful library result | chris | C-corpus-extension | `d00b33bfd20a117c` |  |  |
| `Zeta23Core.vonNeumann_trace_ineq_hermitian` | useful library result | chris | C-corpus-extension | `36af8c92a6839031` |  |  |
| `Zeta23Obstruction.repaired_witness_neg_at_deep_point` | potentially research-significant | admin | C-corpus-extension | `5ccc5b82deba10c2` |  |  |
| `Zeta23Obstruction.repaired_witness_nonneg` | potentially research-significant | admin | C-corpus-extension | `82f76df7c8d3cd62` |  |  |
| `Zeta23Obstruction.tent_combination_neg_on_band` | potentially research-significant | admin | C-corpus-extension | `bc42ba3f8ba5976c` |  |  |
| `Zeta23Redux.LinAlg.eigenvalue_cauchy_schwarz_count` | useful library result | chris | FRONTIER-linalg | `e000ee9b5347dedb` |  |  |
| `Zeta23Redux.LinAlg.integrality_shadow` | useful library result | admin | FRONTIER-linalg | `b2d70f400631de4e` |  |  |
| `Zeta23Redux.LinAlg.qf_add` | useful library result | chris | External | `30f00dfa5fa0a93f` |  |  |
| `Zeta23Redux.LinAlg.quadForm_eq_complex` | useful library result | chris | External | `ac0479c81ec3ba26` |  |  |
| `Zeta23Redux.LinAlg.rank_trace_ineq` | useful library result | chris | FRONTIER-linalg | `99874209dfddde32` |  |  |
| `Zeta23Redux.LinAlg.sq_ge_linear` | useful library result | admin | FRONTIER-linalg | `9462b3dde0bfd7b3` |  |  |
| `Zeta23Redux.LinAlg.sq_ge_linear_two` | useful library result | admin | FRONTIER-linalg | `00860ae030b68c65` |  |  |
| `Zeta23Redux.LinAlg.sum_doublyStochastic_mul_le` | useful library result | chris | External | `e3ff126481db8aac` |  |  |
| `Zeta23Redux.LinAlg.sylvester_hermitian_finrank` | useful library result | chris | FRONTIER-linalg | `e2f4280e35b93515` |  |  |
| `Zeta23Redux.LinAlg.vonNeumann_trace_ineq` | useful library result | admin | FRONTIER-linalg | `03ace1a50fcfaaac` |  |  |
| `Zeta23Scaffold.assembly_window_constants` | routine formalization | admin | A-assembly | `bd2b4c368dc37777` |  |  |
| `Zeta23Scaffold.christoffel_inverse_form` | routine formalization | admin | B-christoffel | `09ceb7f06c301317` |  |  |
| `Zeta23Scaffold.hankel_christoffel_13_18` | routine formalization | chris | B-christoffel | `cedeb06725483043` |  |  |
| `Zeta23Scaffold.Hd_ge_Fwin_iff` | routine formalization | admin | A-assembly | `d82f734a5c9c2f9d` |  |  |
| `Zeta23Scaffold.Hwin_nonneg_iff_threshold` | routine formalization | chris | A-assembly | `20ecd6fc0f8a3b5f` |  |  |
| `Zeta23Scaffold.m2_at_one_assembly` | routine formalization | admin | C-integral | `0ade018bee724fe7` |  |  |
| `Zeta23Scaffold.psiCubic_eq_one_of_small` | routine formalization | admin | A-assembly | `71fa4afaafefa23d` |  |  |
| `Zeta23Scaffold.psiCubic_le_one` | routine formalization | chris | A-assembly | `71b702ed91c1432a` |  |  |
| `Zeta23Scaffold.rung_glue_constant_upgrade` | routine formalization | admin | A-assembly | `ae782b548eab4356` |  |  |

## Appendix B — 197 failing and 2 indeterminate selected target entries

| Target | Gate | Account | AXLE hash | Diagnostic excerpt |
| --- | --- | --- | --- | --- |
| `allowed_classes_zmod_card` | fail | chris | `cf34209d4a36a570` | -:373:137-373:172: error(lean.unknownIdentifier): Unknown identifier `tendsto_inverse_atTop_nhds_zero_nat`  |
| `Aristotle.Formalize_the_Brockian_appr` | fail | chris | `dd5c6cc1a04193fa` | -:3:10-3:13: error: unknown namespace `DSL`  |
| `Aristotle.Summarizes_Brockian_prime_d` | fail | chris | `4c4f1afa61fcbc3d` | -:3:10-3:13: error: unknown namespace `DSL`  |
| `ArithmeticFunction.liouville_apply` | fail | admin | `1fceca078bd0b399` | -:24:4-24:13: error: `ArithmeticFunction.liouville` has already been declared  |
| `Brockian.adjoint_le_adjoint_of_le` | fail | admin | `0e630423514adfa9` | -:395:36-395:43: error: Ambiguous term   map_neg Possible interpretations:   _root_.map_neg : ∀ (f : ?m.167) (a : ?m.165), (f : ?m.165 → ?m.166) (-a) = -(f : ?m.165 → ?m.166) a   … |
| `Brockian.countMultiples_eq_div` | fail | chris | `07ada1ab30ae64b1` | -:140:4-140:73: error: Type mismatch: After simplification, term   Filter.Tendsto.comp tendsto_inv_atTop_zero hlog  has type   @Filter.Tendsto ℕ ℝ ((fun (r : ℝ) => r⁻¹) ∘ fun (N :… |
| `Brockian.Equidistribution.coe_fract` | fail | admin | `9ce722778bdb9cc4` | -:81:57-81:61: error: `ring_nf` made no progress on the goal  |
| `Brockian.Equidistribution.equidistribution_of_asymptotic` | fail | admin | `e136c183b2ebcf3b` | -:177:11-177:35: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern   ‖-?x + ?y‖ in the target expression   ‖f - g‖ < ε / 3  x : ℕ → AddCircle 1 hx :   ∀ (k… |
| `Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform` | fail | chris | `b45eab5ba43654bf` | -:92:40-92:41: error: Application type mismatch: The argument   f has type   α → ℝ of sort `Type u_1` but is expected to have type   Monotone ?m.357 of sort `Prop` in the applicat… |
| `Brockian.eVariationOn_sub_le` | fail | admin | `cb9941a1e49fed3b` | -:75:40-75:41: error: Application type mismatch: The argument   f has type   α → ℝ of sort `Type u_1` but is expected to have type   Monotone ?m.402 of sort `Prop` in the applicat… |
| `Brockian.EvenPerfectMod9.euclidEuler_form_mod9` | fail | chris | `c56350f2e1de858c` | -:42:16-42:39: error(lean.unknownIdentifier): Unknown identifier `nat_sub_dvd_pow_sub_pow`  |
| `Brockian.EvenPerfectMod9.sigma_two_pow_eq_mersenne_succ_main` | fail | chris | `cc2eb5ce20d5d511` | -:104:6-104:30: error: Type mismatch: After simplification, term   Nat.ModEq.mul hpow0 hm  has type   2 ^ (6 * q) * mersenne (6 * q + 1) ≡ 1 [MOD 9] but is expected to have type  … |
| `Brockian.EvenPerfectTriangular.even_perfect_triangular` | fail | chris | `c94a87a7f657cbbe` | -:14:4-14:65: error(lean.unknownIdentifier): Unknown identifier `Theorems100.Nat.eq_two_pow_mul_prime_mersenne_of_even_perfect`  |
| `Brockian.fourier_lineDerivOp_sq` | fail | chris | `ac0db80bc97c2d83` | -:106:4-106:20: error: Type mismatch: After simplification, term   this  has type   @Function.HasTemperateGrowth V V inst✝¹ inst✝.toNormedSpace inst✝¹ inst✝.toNormedSpace     (⇑((… |
| `Brockian.FreeLaplacianPlancherel.freeLaplacian_essentiallySelfAdjoint_via_plancherel` | fail | chris | `8ba174f9959427b2` | -:331:14-331:16: error: unexpected token 'φ'; expected '(', '[', '_', '{', '⦃' or identifier  |
| `Brockian.GoldenRatio.pos` | fail | chris | `56d937fab74c9ad0` | -:105:6-105:187: error: Type mismatch: After simplification, term   mul_lt_mul_of_pos_right (a✝ ih)     (_root_.div_pos       (add_pos zero_lt_one         (Real.sqrt_pos.mpr      … |
| `Brockian.GraphAcyclic.side_invariant` | fail | chris | `4c64e95fd9e14d4e` | -:11:23-11:43: error: Invalid `⟨...⟩` notation: The expected type of this term could not be determined  |
| `Brockian.haar_eq_volume` | fail | admin | `4e2c4c1c8859fb53` | -:159:8-159:69: error: Type mismatch: After simplification, term   Brockian.EquidistributionBVReduction.tendsto_avg_fourier hirr hk  has type   @Filter.Tendsto ℕ ℂ     (fun (N : ℕ… |
| `Brockian.integrable_continuousMap` | fail | admin | `eda96a10f3d11f2d` | -:282:2-282:32: error: Type mismatch: After simplification, term   h2  has type   @Filter.Tendsto ℕ ℝ     (Complex.re ∘ fun (N : ℕ) => (↑(Brockian.EquidistributionBVReduction.avg … |
| `Brockian.LandauNSquaredPlusOne.LandauFourthConjecture` | fail | chris | `c1ccdacc14aff908` | -:112:37-112:85: error: Type mismatch: After simplification, term   Int.prime_iff_natAbs_prime.mp hprime  has type   Nat.Prime ((↑m : ℤ) ^ 2 + 1).natAbs but is expected to have ty… |
| `Brockian.LegendreConjecture.LegendreConjecture` | indeterminate | admin | `` | no hash/environment/diagnostic recorded |
| `Brockian.LegendreThreeSquare.QF_conj` | fail | chris | `a34476b63ac80fe0` | -:561:27-566:8: error: unsolved goals C : Matrix (Fin 2) (Fin 2) ℤ hsym : C.IsSymm hpos : PosDefZ C hdet : C.det = 1 v : Fin 2 → ℤ hv : QF C v = 1 w : Fin 2 → ℤ := C *ᵥ v h : v 0 … |
| `Brockian.LegendreThreeSquare.sum_three_squares_iff` | fail | chris | `703c753ddf76c4ed` | -:10:10-10:62: error(lean.unknownIdentifier): Unknown identifier `GeometryOfNumbers.not_exception_of_sum_three_squares`  |
| `Brockian.MersennePerfect.MersennePrimeInfinitude` | fail | admin | `fcb9c866bd10b8c5` | -:64:2-64:38: error(lean.unknownIdentifier): Unknown identifier `Theorems100.Nat.even_and_perfect_iff`  |
| `Brockian.OddPerfectThreePrimes.geomSum_mul_pred` | fail | chris | `32a777abc294c795` | -:12:2-12:11: error: `simp` made no progress  |
| `Brockian.phi_pos` | fail | chris | `6e69bec61a2c82bf` | -:190:74-192:34: error: unsolved goals case e'_2 t : ℝ ⊢ deriv (fun t => cexp (↑t + ↑t * ↑«φ» * I)) t = deriv (cexp ∘ fun y => ↑«φ» * I * ↑y + ↑y) t  case e'_3 t : ℝ ⊢ (1 + ↑«φ» *… |
| `Brockian.QuasiperfectNumbers.QuasiperfectExists` | fail | admin | `75ef88a5407ca676` | -:105:30-105:56: error: Type mismatch: After simplification, term   Dvd.dvd.neg_right hdvd  has type   @Dvd.dvd ℤ semigroupDvd (↑N : ℤ) (-1 + -(↑m : ℤ)) but is expected to have ty… |
| `Brockian.Ramanujan7.qb_succ_succ` | fail | chris | `9ce9cc792f3cae0c` | -:1242:6-1242:29: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern   ?m.35 ∈ Finset.antidiagonal ?m.32 ?m.33 ?m.34 in the target expression   p ∈ HasAntid… |
| `Brockian.SieveHamiltonian.twin_pins_mod_three` | fail | chris | `fcd65d8db978e612` | -:62:48-63:55: error: unsolved goals case «1» ⊢ 1 = 1  |
| `Brockian.sqrt_block` | fail | chris | `682e7e2723e11aaf` | -:117:4-117:15: error(lean.unknownIdentifier): Unknown identifier `windowCount`  Note: It is not possible to treat `windowCount` as an implicitly bound variable here because the `… |
| `Brockian.SuperperfectNumbers.OddSuperperfectExists` | fail | chris | `aee00e1096c63155` | false result with no diagnostic recorded |
| `Brockian.SylvesterSchur.sylvester_schur` | fail | chris | `afefab547852d804` | -:9:4-9:41: error(lean.unknownIdentifier): Unknown identifier `Erdos699Formalization.sylvester_schur`  |
| `Brockian.upperFn_nonneg` | fail | chris | `0c2136332ac01952` | -:50:5-50:18: error: unknown namespace `Brockian.Weyl`  |
| `Brockian.WeirdNumbers.OddWeirdExists` | fail | chris | `ca2be211ce9a387e` | false result with no diagnostic recorded |
| `Brockian.Weyl.DeficiencyODE.locallyIntegrable_potential_mul` | fail | chris | `da63f677aa6c3b92` | -:98:17-98:25: error(lean.unknownIdentifier): Unknown identifier `IsBumpOn`  Note: It is not possible to treat `IsBumpOn` as an implicitly bound variable here because the `autoImp… |
| `Brockian.Weyl.DeficiencyODE.norm_subI_sq` | fail | chris | `d3095b74389c4e0c` | -:287:2-287:29: error: Type mismatch   Module.Basis.span_apply ?m.24 n has type   (Module.Basis.span ?m.24 : ℕ → ↥(Submodule.span ?m.18 (Set.range ?m.23))) n = ⟨?m.23 n, ⋯⟩ but is… |
| `Brockian.Weyl.DeficiencyODE.schrodinger_essentiallySelfAdjoint_of_weakRegularity` | fail | chris | `c751192f3e83828a` | -:88:47-88:50: error: Invalid projection: Projection operates on types of the form `C ...` where C is a constant. The expression   v has type `H` which does not have the necessary… |
| `Brockian.Weyl.dense_range_iff_forall_inner_eq_zero` | fail | admin | `d55ba5fbcb2932ad` | -:500:60-500:63: error(lean.unknownIdentifier): Unknown identifier `L2R`  Note: It is not possible to treat `L2R` as an implicitly bound variable here because the `autoImplicit` o… |
| `Brockian.Weyl.DichotomyTarget.radius_tendsto_zero_iff_counterexample` | fail | chris | `ac796fa94c35bbb8` | -:82:4-82:64: error: Type mismatch: After simplification, term   Tendsto.comp tendsto_inv_atTop_zero hprod  has type   @Tendsto ℝ ℝ ((fun r => r⁻¹) ∘ fun b => 2 * c * I b) atTop (… |
| `Brockian.Weyl.FreeLaplacian2.continuous_symbol` | fail | chris | `5f71aa9006151189` | -:80:31-80:32: error: unexpected token 'φ'; expected '_' or identifier  |
| `Brockian.Weyl.FreeLaplacian2.freeLaplacian_essentiallySelfAdjoint_of_fourier` | fail | chris | `f70e3c42a919628f` | -:221:62-221:68: error: Application type mismatch: The argument   hminus has type   Dense (↑(Brockian.Weyl.defRange T (-Complex.I)) : Set H) of sort `Prop` but is expected to have… |
| `Brockian.Weyl.FreeLaplacian2.norm_sub_I_smul_sq` | fail | admin | `a1bc6c91f63a57fb` | -:177:10-177:11: error: Invalid pattern variable: Variable name must be atomic, but `Nat.totient._@.1126475629._hygCtx._hyg.1997` has multiple components  |
| `Brockian.Weyl.SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode` | fail | chris | `982f1843ba4c988d` | -:94:8-94:10: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern   w in the target expression   Complex.addCommGroup = Complex.instNormedAddCommGroup.toAddC… |
| `Brockian.Weyl.WeylLawTarget.counting_diverges_of_candidate` | fail | admin | `114628ad60226354` | -:93:26-93:53: error: Type mismatch: After simplification, term   Nat.cast_le.mpr h  has type   @LE.le ℕ Nat.instPartialOrder.toLE (↑x✝¹ : ℕ) (↑x✝ : ℕ) but is expected to have typ… |
| `Brockian.WilsonPrimes.WilsonPrimeInfinitude` | fail | admin | `3d5d15797233f3ff` | false result with no diagnostic recorded |
| `BrockianFoundations.phi_pos` | fail | chris | `125ae1171ff55996` | -:48:8-48:10: error: unexpected token 'φ'; expected identifier  |
| `BrockianFramework.golden_ratio_quadratic` | fail | chris | `75cc80ee3df87241` | -:76:9-76:29: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern   ↑(Nat.fib n) in the target expression   («φ» ^ (n + 1) - φ_bar ^ (n + 1)) / √5 + («φ» ^ n… |
| `brockianSpiral_continuous` | fail | chris | `2bb26d01ea82edbf` | -:68:81-84:24: error: unsolved goals k α : ℝ h_cont : Continuous fun t => ↑(k * t) * cexp (twoPiI * ↑(t.rpow α)) ⊢ brockianSpiral k α = fun t => ↑(k * t) * cexp (twoPiI * ↑(t.rpow… |
| `BZFC.BrockRay.residue_le_four` | fail | chris | `a63cf11194f51d1a` | -:151:52-151:56: error: `ring_nf` made no progress on the goal  |
| `C2.BSieve3.lf_pos_eight` | fail | chris | `e047c1003f8866ac` | -:36:2-36:38: error: Type mismatch: After simplification, term   Finset.card_le_card hsub  has type   @LE.le ℕ instLENat (Finset.image (fun x => x % p) G).card p but is expected t… |
| `C4.An6.taylor_zeroth` | fail | admin | `a433620c9df7ba92` | -:9:2-9:34: error: Type mismatch: After simplification, term   this  has type   @Tendsto ℝ ℝ (f ∘ fun x_1 => x + x_1) (𝓝 0) (𝓝 (f x)) but is expected to have type   @Tendsto ℝ ℝ… |
| `card_admissibleLabels` | fail | chris | `a5a20d9f8fd18b24` | -:57:43-57:47: error: Ambiguous term   sqrt Possible interpretations:   √5 : ℝ      Complex.sqrt 5 : ℂ  |
| `Chem.alkane_tree` | fail | chris | `baceed4d349ba818` | -:90:6-90:38: error: Tactic `rewrite` failed: motive is not type correct:   fun (_a : Set V) => _a.ncard = G.degree v Error: Application type mismatch: The argument   fun (a : V) … |
| `Chem.huckel_C11` | fail | admin | `86d0567de363cc4d` | -:121:13-121:39: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern   ((↑?M : Matrix ?m.129 ?m.129 ?m.127) * ?N * (↑?M : Matrix ?m.129 ?m.129 ?m.127)⁻¹).cha… |
| `Chem.huckel_C13` | fail | admin | `35745eaa98eadd0a` | -:175:10-175:36: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern   (↑?M * ?N * (↑?M)⁻¹).charpoly in the target expression   (↑u * Matrix.diagonal eval13 … |
| `Chem.huckel_C14` | fail | admin | `165aba540915bda0` | -:166:10-166:36: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern   ((↑?M : Matrix ?m.110 ?m.110 ?m.108) * ?N * (↑?M : Matrix ?m.110 ?m.110 ?m.108)⁻¹).cha… |
| `Chem.huckel_C15` | fail | chris | `76eb9f2539005cd8` | -:138:17-138:43: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern   (↑?M * ?N * (↑?M)⁻¹).charpoly in the target expression   (↑F_isUnit.unit * D * ↑F_isUn… |
| `Chem.huckel_C16` | fail | chris | `2422ded83c5b26f5` | -:176:13-176:39: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern   (↑?M * ?N * (↑?M)⁻¹).charpoly in the target expression   ((↑u * Matrix.diagonal fun k … |
| `Chem.huckel_C19` | fail | chris | `cfc9836d59dfc66a` | -:46:71-47:78: error: unsolved goals i j : ZMod 19 ⊢ (if i - j = 1 ∨ j - i = 1 then 1 else 0) = if i - j = 1 ∨ j - i = 1 then 1 else 0  |
| `Chem.huckel_C20` | fail | admin | `7739ab446643975e` | -:109:35-109:53: error: ring failed, ring expressions not equal i : Fin 20 h : i - 1 = i + 1 ⊢ -2 + 2 = 0  |
| `Chem.huckel_C8` | fail | admin | `6b9aa25d152f452a` | -:192:10-192:36: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern   (↑?M * ?N * (↑?M)⁻¹).charpoly in the target expression   (↑dftUnit * eigDiag * ↑dftUni… |
| `Chem.huckel_C9` | fail | admin | `115f281e55ef733b` | -:119:13-119:39: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern   (↑?M * ?N * (↑?M)⁻¹).charpoly in the target expression   (↑U * D * ↑U⁻¹).charpoly = ∏ … |
| `Chem.huckel_cycle_spectrum` | fail | admin | `6a85f5d062b0f340` | -:132:10-132:36: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern   (↑?M * ?N * (↑?M)⁻¹).charpoly in the target expression   ((↑u * diagonal fun k => ↑(hu… |
| `Chem.polya_isomer_count` | fail | chris | `0c9366fc6d69e95e` | -:78:4-78:36: error: Type mismatch: After simplification, term   this x  has type   @Eq C (F ⟦g⁻¹ • x⟧) (F ⟦x⟧) but is expected to have type   @Eq C ((g • fun (x : X) => F ⟦x⟧) x)… |
| `CS.baker_gill_solovay` | fail | chris | `641068b768b8da50` | -:63:11-63:17: error(lean.unknownIdentifier): Unknown identifier `Oracle`  Note: It is not possible to treat `Oracle` as an implicitly bound variable here because the `autoImplici… |
| `CS.church_rosser_beta_diamond` | fail | admin | `a82436f4a8c11c55` | -:22:28-22:41: error: Function expected at   app but this term has type   ?m.3  Note: Expected a function because this term is being applied to the argument   (lam a)  Hint: The i… |
| `CS.dijkstra_correct` | fail | admin | `1dfa8ba25dad224f` | -:63:74-63:83: error: Function expected at   zero_le but this term has type   0 ≤ ?m.14  Note: Expected a function because this term is being applied to the argument   _  |
| `CS.huffman_optimal` | fail | admin | `3f7de031825ae20e` | -:275:2-275:55: error: Type mismatch: After simplification, term   this  has type   @Eq ℝ (map ((fun n => (2 ^ n)⁻¹) ∘ Prod.snd) S).sum (map ((fun n => (2 ^ n)⁻¹) ∘ Prod.snd) T).s… |
| `CS.kleene_regex_dfa` | fail | admin | `835778d9e622b230` | -:126:10-126:28: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern   @Membership.mem (List ?m.219) (Language ?m.219) Language.instMembershipList ?m.220∗ ?m… |
| `CS.pumping_regular` | fail | chris | `2a3b4d1aafab5eac` | -:46:6-46:24: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern   @Membership.mem (List ?m.209) (Language ?m.209) Language.instMembershipList (KStar.kstar … |
| `CS.savitch` | fail | chris | `87ccbe68a6831fb2` | -:25:4-25:12: error: Function expected at   NSPACE but this term has type   ?m.1  Note: Expected a function because this term is being applied to the argument   f  Hint: The ident… |
| `CS.sorting_lb_4` | fail | chris | `68d1ba311c84398a` | -:127:4-127:61: error: Type mismatch: After simplification, term   hsm  has type   @StrictMono (Fin n) ℕ Fin.instPartialOrder.toPreorder Nat.instPreorder     ((fun (i : Fin n) => … |
| `D5_card` | fail | chris | `8f7aa82870d7f114` | -:103:3-103:5: error: unexpected token 'φ'; expected identifier  |
| `D5.card` | fail | chris | `8f7aa82870d7f114` | -:103:3-103:5: error: unexpected token 'φ'; expected identifier  |
| `D5Structure.phi_squared` | fail | chris | `af05811f23b19993` | -:447:45-447:94: error: `simp` made no progress  |
| `edgeMat_psd` | fail | chris | `7cce2749709f2186` | -:66:4-66:56: error: `simp` made no progress  |
| `epsilonLight_of_sumAv` | fail | chris | `2f3cc69d77f3cf04` | -:74:4-74:18: error: Tactic `introN` failed: There are no additional binders or `let` bindings in the goal to introduce  V : Type u_1 inst✝¹ : Fintype V inst✝ : DecidableEq V G : … |
| `F₂_zero_at_prime` | fail | chris | `2f71395d8b4176e2` | -:43:58-43:59: error(lean.unknownIdentifier): Unknown identifier `σ`  |
| `FirstProofQ6.laplacian_eq_sum_sq` | fail | chris | `568dc566484ad207` | -:111:8-111:14: error: found a proof, but the corresponding tactic failed:   (expose_names; exact fun x_2 a h =>     (fun {a b} [Decidable a] [Decidable b] => Decidable.or_iff_not… |
| `FirstProofQ6.psdLe_refl` | fail | chris | `25a6fa641dd896ba` | -:106:8-106:32: error: invalid `▸` notation, expected result type of cast is    0 ≤ x.sum fun i xi => x.sum fun j xj => xi * (xj * ((e u i - e v i) * (e u j - e v j))) however, th… |
| `Frontier.Aronszajn_tree_exists` | fail | admin | `d5afc226142e1d1d` | -:54:60-54:74: error: Ambiguous term   mk_Iio_ordinal Possible interpretations:   Cardinal.mk_Iio_ordinal : ∀ (o : Ordinal.{?u.12}),     #(↑(Set.Iio o) : Type (?u.12 + 1)) = Cardi… |
| `Frontier.aumann_agreement` | fail | admin | `3f746eedbbadc3d2` | -:7:2-7:27: error(lean.unknownIdentifier): Unknown identifier `Frontier.aumann_agreement`  |
| `Frontier.Banach_Tarski` | fail | chris | `f9b9fded096291ab` | -:322:27-322:30: error(lean.synthInstanceFailed): failed to synthesize instance of type class   Norm E  Hint: Type class instance resolution failures can be inspected with the `se… |
| `Frontier.bcs_gap_binding` | fail | chris | `6b66990f0789ed18` | -:50:2-50:12: error: `field_simp` made no progress on the goal  |
| `Frontier.berry_phase_quantized` | fail | admin | `b0c240134b5ce73a` | -:69:6-71:86: error: Type mismatch: After simplification, term   Continuous.neg     (Continuous.clm_apply       (ContDiff.continuous_fderiv hc1         (Mathlib.Meta.NormNum.isNat… |
| `Frontier.Brun_twin_reciprocal` | fail | chris | `7c064f3275f3baf3` | -:32:21-32:39: error(lean.unknownIdentifier): Unknown identifier `Brun.twinIndicator`  |
| `Frontier.Chen_theorem` | fail | chris | `2f1e0b094f098e48` | false result with no diagnostic recorded |
| `Frontier.chsh_pointwise_le_two` | fail | admin | `03ca8e2af8140007` | -:136:66-138:10: error: unsolved goals ⊢ (MeasureTheory.Measure.dirac ()).real Set.univ + (MeasureTheory.Measure.dirac ()).real Set.univ = 2  |
| `Frontier.cook_levin` | fail | chris | `1156fd5c9d160ed4` | -:39:4-39:9: error: Function expected at   SAT but this term has type   ?m.2  Note: Expected a function because this term is being applied to the argument   F  Hint: The identifie… |
| `Frontier.duminil_ising_sharp` | fail | admin | `e1990eec4fa5717f` | -:117:8-117:55: error: Type mismatch: After simplification, term   HasDerivAt.neg (HasDerivAt.const_mul a (hasDerivAt_id x))  has type   @HasDerivAt ℝ DenselyNormedField.toNontriv… |
| `Frontier.exotic_R4` | fail | admin | `ccdb3846c1d8ba9a` | -:75:12-75:33: error(lean.unknownIdentifier): Unknown identifier `transportChartedSpace`  |
| `Frontier.figalli_OT_regularity` | fail | admin | `380c391ee4209fb3` | -:99:8-99:35: error: Type mismatch: After simplification, term   this  has type   @HasDerivAt ℝ DenselyNormedField.toNontriviallyNormedField ℝ Real.normedCommRing.toCommRing.toAdd… |
| `Frontier.friendship_theorem` | fail | chris | `d5739a708acc7735` | -:63:36-63:41: error: Application type mismatch: The argument   hsymm has type   Symmetric friend but is expected to have type   autoParam (Std.Symm friend) SimpleGraph.symm._auto… |
| `Frontier.hairer_KPZ` | fail | chris | `2e5ec6a80992c08a` | -:170:19-170:27: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern   v 0 x in the target expression   (fun t x => rexp (v t x)) 0 x = rexp (u₀ x)  xi : ℝ →… |
| `Frontier.ham_sandwich` | fail | admin | `8cc8a2c706bdc73a` | -:63:25-63:34: error: Function expected at   zero_le but this term has type   0 ≤ ?m.58  Note: Expected a function because this term is being applied to the argument   m  |
| `Frontier.hodge_statement` | fail | admin | `2ef85899d2bbd512` | -:69:4-69:16: error(lean.dependsOnNoncomputable): failed to compile definition, consider marking it as 'noncomputable' because it depends on 'instCommCStarAlgebraComplex', which i… |
| `Frontier.huang_sensitivity` | fail | admin | `0b8473fc0017002b` | -:149:19-149:32: error(lean.unknownIdentifier): Unknown identifier `Sensitivity.Q`  |
| `Frontier.Hydra_Kirby_Paris` | fail | chris | `eddc686c75ae7f61` | -:230:2-230:22: error: Type mismatch: After simplification, term   Or.inr h  has type   (Hydra.node [Hydra.node [Hydra.node []]]).CutTop       (Hydra.node [Hydra.node [], Hydra.no… |
| `Frontier.inaccessible_implies_ConZFC` | fail | chris | `b9a5099a923ee18c` | -:506:67-511:82: error: unsolved goals M : Type u_1 inst✝ : setLang.Structure M n : ℕ φ : setLang.BoundedFormula Empty (n + 1) ⊢ (∀ (xs : Fin n → M) (a : M),       ∃ a_1,         … |
| `Frontier.isP2_of_prime` | fail | chris | `e1f1f3ea4161c56a` | false result with no diagnostic recorded |
| `Frontier.jones_polynomial_invariant` | fail | admin | `8abb82dee387716d` | -:128:2-128:28: error: Type mismatch: After simplification, term   this  has type   @Eq R (K.br (K.plug C (a * K.xp i * b)))     ((↑K.A : R) * K.br (K.plug C (a * b)) + (↑K.A⁻¹ : … |
| `Frontier.landau_levels` | fail | chris | `984e33699656c1f9` | -:112:4-112:8: error: `ring_nf` made no progress on the goal  |
| `Frontier.langlands_reciprocity` | fail | admin | `eef25e6562757b0c` | -:190:11-190:63: error(lean.synthInstanceFailed): failed to synthesize instance of type class   IsCyclotomicExtension {m} ℚ (CyclotomicField m ℚ)  Hint: Type class instance resolu… |
| `Frontier.lieb_robinson` | fail | admin | `2a32fe44bb8baab2` | -:101:4-101:20: error: Type mismatch: After simplification, term   this  has type   @HasDerivAt ℝ DenselyNormedField.toNontriviallyNormedField A NonUnitalNormedRing.toNormedAddCom… |
| `Frontier.Loeb_theorem` | fail | admin | `57abdccb399045c9` | -:32:4-32:8: error(lean.invalidDottedIdent): Invalid dotted identifier notation: The expected type of `.var`   Trm is not of the form `C ...` or `... → C ...` where C is a constan… |
| `Frontier.lovasz_kneser` | fail | chris | `eac12671d7fbe513` | -:55:11-55:12: error: Tactic `introN` failed: There are no additional binders or `let` bindings in the goal to introduce  n k : ℕ ⊢ Std.Symm fun (s t : Frontier.KneserVertex n k) … |
| `Frontier.mirzakhani_WP_volume` | fail | admin | `bd98864983500197` | -:102:6-102:11: error: Failed to rewrite using equation theorems for `mirzH`  |
| `Frontier.navier_stokes_regularity` | fail | admin | `b84fe085e0d54271` | -:132:4-132:31: error: Type mismatch: After simplification, term   hw  has type   SmoothScalarField w but is expected to have type   ContDiff ℝ ∞ fun x => w x.1 x.2  |
| `Frontier.ngo_fundamental_lemma` | fail | chris | `32e3a6cf12e1cc09` | -:203:8-203:22: error: Type mismatch: After simplification, term   h'  has type   @Eq (prodDatum D E).GClass (a, b) gG but is expected to have type   @Eq (D.GClass × E.GClass) (a,… |
| `Frontier.nirenberg_gagliardo` | fail | admin | `83c1afe100610190` | -:93:4-93:65: error: Type mismatch: After simplification, term   HasDerivAt.pow (hd y) 2  has type   @HasDerivAt ℝ DenselyNormedField.toNontriviallyNormedField ℝ Real.normedCommRi… |
| `Frontier.NTClassics.fermat_little` | fail | chris | `086d38a7c793785d` | -:16:76-18:19: error: unsolved goals h : {p \\| Nat.Prime p ∧ p ≡ 3 [MOD 4]}.Infinite x✝ : ℕ ⊢ Nat.Prime x✝ ∧ x✝ % 4 = 3 ↔ Nat.Prime x✝ ∧ x✝ ≡ 3 [MOD 4]  |
| `Frontier.Paris_Harrington` | fail | admin | `08e37498deca43a0` | -:71:49-71:59: error(lean.synthInstanceFailed): failed to synthesize instance of type class   UsesSetNotationForOrder { T // T.Infinite }  Hint: Type class instance resolution fai… |
| `Frontier.penrose_singularity` | fail | admin | `b9b0ff44abd54aeb` | -:86:4-86:50: error: Type mismatch: After simplification, term   HasDerivAt.inv (hderiv t ht) h0  has type   @HasDerivAt ℝ DenselyNormedField.toNontriviallyNormedField ℝ     Dense… |
| `Frontier.Spectral.cycle_gap_vanishes` | fail | admin | `b2b9cde6be0a7fd7` | -:49:2-49:27: error: Type mismatch: After simplification, term   h2  has type   @Filter.Tendsto ℕ ℝ (fun (x : ℕ) => 2 - 2 * Real.cos (2 * π / (↑x : ℝ))) Filter.atTop (nhds 0) but … |
| `Frontier.Spectral.expander_uniform_gap_witness` | fail | chris | `445bbfea194de2ed` | -:80:11-80:12: error: Tactic `introN` failed: There are no additional binders or `let` bindings in the goal to introduce  k : ℕ ⊢ Std.Symm fun x y => ∃ i, y = cflip i x  |
| `Frontier.uhlenbeck_bubbling` | fail | chris | `962bb4a077cdf07b` | -:249:5-249:15: error: invalid binder annotation, type is not a class instance   MeasureTheory.NoAtoms mu  Note: Use the command `set_option checkBinderAnnotations false` to disab… |
| `Frontier.Vinogradov_three_primes` | fail | chris | `e7d50ae89b27513f` | false result with no diagnostic recorded |
| `Frontier.voevodsky_milnor` | fail | admin | `9ea156581749f235` | -:74:4-74:22: error(lean.dependsOnNoncomputable): failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Finsupp.instAddCommMonoid', which is … |
| `Frontier.yang_mills_mass_gap` | fail | chris | `3c55ead1e798ab0a` | -:267:78-268:23: error: unsolved goals a : ℝ v : ↥HS ⊢ (a • ContinuousLinearMap.id ℂ ↥HS) v = a • v  |
| `Frontier.zelmanov_restricted_burnside` | fail | admin | `a610154a7c5a9e77` | -:220:6-220:81: error: Type mismatch: After simplification, term   congrArg (⇑Additive.ofMul : G → Additive G) (hexp ((Additive.toMul : Additive G → G) x))  has type   @Eq G ((Add… |
| `gamma_lt_log_four_pi` | fail | chris | `37af928250eeb850` | -:90:4-90:60: error: unsolved goals s : ℂ hs : 1 < s.re ⊢ ∑' (k : ℕ), -(((2 + ↑k * 2) ^ s)⁻¹ * (-1) ^ (k * 2)) = -∑' (n : ℕ), ((2 + ↑n * 2) ^ s)⁻¹  |
| `goldbach_from_count` | fail | chris | `ad937f654890005e` | -:241:16-241:39: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern   deriv ⇑ofRealCLM ?m.277 in the target expression   deriv (fun t => cexp (↑t * (1 + ↑ph… |
| `golden_fundamental` | fail | chris | `6c97b21afe21139d` | -:66:3-66:5: error: unexpected token 'φ'; expected identifier  |
| `GoldenRatio.pos` | fail | chris | `15d3972121896979` | -:284:15-284:35: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern   ↑(fib n) in the target expression   (phi ^ (n + 1) - phi_bar ^ (n + 1)) / √5 + (phi ^ … |
| `H_op_is_self_adjoint` | fail | chris | `59832bc7047ccf02` | -:113:26-113:35: error: linarith failed to find a contradiction ψ : L2_Modular_Level5 a✝ : -(ψ.im * (6 * ψ.im)) < -6 * (↑‖ψ‖ ^ 2).re + ψ.re * (6 * ψ.re) ⊢ False failed  |
| `HarmonicArch.ray_add` | fail | chris | `f6f08158bd71a1a5` | -:175:44-175:51: error: Tactic `assumption` failed  case zero hj : 0 < 4 ⊢ rotate (rotate (rotate (rotate ⟨0, hj⟩))) = ⟨0, hj⟩  |
| `HarmonicArch.ray_unique` | fail | chris | `edce2b6fbd157a67` | -:148:44-148:51: error: Tactic `assumption` failed  case zero hj : 0 < 4 ⊢ rotate (rotate (rotate (rotate ⟨0, hj⟩))) = ⟨0, hj⟩  |
| `induced_laplacian_quad_form` | fail | chris | `5d90319a65601e2d` | -:82:14-85:46: error: unsolved goals V : Type u_1 inst✝¹ : Fintype V inst✝ : DecidableEq V G✝ : SimpleGraph V S : Finset V x✝ : V → ℝ G : SimpleGraph ↥S x : ↥S → ℝ i : ↥S a : Sym2… |
| `L2Layer.MulOpData.memLp_infinity` | fail | chris | `912584503656cd74` | -:140:8-140:41: error: unknown goal  |
| `laplacian_quadratic_form` | fail | chris | `a587706c5fd74142` | -:79:10-79:16: error: found a proof, but the corresponding tactic failed:   (expose_names; exact fun a ha =>     (fun {α} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] a b => (… |
| `laplacian_symmetric` | fail | chris | `5e830d6c1bfebc01` | -:109:17-109:19: error: unexpected token 'φ'; expected identifier  |
| `Math.abel_ruffini_deg5` | fail | chris | `d2078a810d809dbd` | -:74:66-76:89: error: unsolved goals case e'_4 R : Type u_1 inst✝¹ : CommRing R a b : ℕ inst✝ : Nontrivial R this : (Polynomial.X ^ 5 - (Polynomial.C : R → R[X]) (↑a : R) * Polyno… |
| `Math.brouwer_2d` | fail | chris | `834a292bde447490` | -:88:31-89:71: error(lean.synthInstanceFailed): failed to synthesize instance of type class   LocallyPathConnectedSpace ↑(closedBall 0 1)  Hint: Type class instance resolution fai… |
| `Math.euler_pentagonal` | fail | chris | `044730d1dd602ed1` | -:47:26-47:42: error(lean.unknownIdentifier): Unknown identifier `Franklin.pentExp`  |
| `Math.gauss_bonnet_polygon` | fail | chris | `0d8eeb7aff72a826` | -:59:8-59:21: error(lean.unknownIdentifier): Unknown identifier `volume_sector`  |
| `Math.halls_marriage` | fail | admin | `45bd968348c58278` | -:54:20-54:27: error: Tactic `introN` failed: There are no additional binders or `let` bindings in the goal to introduce  L : Type u_1 R : Type u_2 inst✝³ : Fintype L inst✝² : Fin… |
| `Math.ramsey_3_4` | fail | admin | `aeba9661369ccd42` | -:50:23-50:72: error: Application type mismatch: The argument   SimpleGraph.Embedding.comap (Fin.castLEEmb h) G has type   SimpleGraph.comap (⇑(Fin.castLEEmb h) : Fin m → Fin n) G… |
| `Math.ramsey_3_5` | fail | admin | `17d3055bf5564ef7` | -:152:29-152:59: error: Invalid `⟨...⟩` notation: The expected type of this term could not be determined  |
| `Math.ramsey_4_4` | fail | chris | `0d90525102b6ea8b` | -:122:2-122:27: error: Type mismatch: After simplification, term   hsplit  has type   @Eq ℕ (#({y ∈ S \\| G.Adj v y}) + (#(Math.blueN G S v) + 1)) #S but is expected to have type  … |
| `Math.sperner_lemma` | fail | chris | `59ebf36a945c093d` | -:395:6-395:45: error: Type mismatch   Math.sum_card_filter_comm fun (s t : ?m.1101) => ?m.1107 has type   ∑ a ∈ ?m.1103, #({b ∈ ?m.1104 \\| ?m.1107}) = ∑ b ∈ ?m.1104, #({a ∈ ?m.11… |
| `mem_ray_iff` | fail | chris | `61dbc7c4f77aabc4` | -:189:367-189:372: error: `ring_nf` made no progress on the goal  |
| `MS.Inequalities.cauchy_schwarz` | fail | chris | `16a95a838f20eb1a` | -:16:2-16:11: error: `simp` made no progress  |
| `MS.Topology.brouwer_fixed_point` | fail | admin | `70406aa6a56c255d` | -:9:2-9:28: error(lean.unknownIdentifier): Unknown identifier `Brouwer.brouwer_closedBall`  |
| `MS2.Combinatorics2.catalan_recurrence` | fail | chris | `0a4384c4921a4e9a` | -:49:46-49:96: error(lean.synthInstanceFailed): failed to synthesize instance of type class   Fintype { t // t.IsTree }  Hint: Type class instance resolution failures can be inspe… |
| `MS2.NTG2.wolstenholme_weak` | fail | chris | `70745e2603aa8f2d` | -:45:2-45:36: error(lean.unknownIdentifier): Unknown identifier `ThreeSquares.nat_sum_three_squares`  |
| `norm_mul_le_bound` | fail | chris | `ed65ba2dbd35365b` | -:39:32-39:36: error: Ambiguous term   sqrt Possible interpretations:   √5 : ℝ      Complex.sqrt 5 : ℂ  |
| `nu_p_eq_image_card` | fail | chris | `7309c424f92ea577` | -:89:2-89:5: error(lean.unknownIdentifier): Unknown identifier `lim`  |
| `PCA.Isolation.priv_escape_monotone` | fail | admin | `71967cdd9a6c3756` | -:192:56-192:58: error: Application type mismatch: The argument   hr has type   P.Reach s d of sort `Prop` but is expected to have type   C of sort `Type u_1` in the application  … |
| `PenroseTiling.sqrt5_gt_one` | fail | chris | `3bda3dde6afa20a2` | -:42:32-42:36: error: Ambiguous term   sqrt Possible interpretations:   Complex.sqrt 5 : ℂ      √5 : ℝ  |
| `pentagon_chord_formula` | fail | chris | `02710e5d54926d0e` | -:48:25-48:27: error: unexpected token 'φ'; expected identifier  |
| `phi_equation` | fail | chris | `90076a20dff3e553` | -:121:46-121:53: error: Tactic `assumption` failed  case zero hj : 0 < 4 ⊢ rotate (rotate (rotate (rotate ⟨0, hj⟩))) = ⟨0, hj⟩  |
| `phi_minimal_polynomial` | fail | chris | `b018e1ec196a8c40` | -:39:11-39:13: error: unexpected token 'φ'; expected identifier  |
| `phi_squared` | fail | chris | `7961a72dc6ea3e6f` | -:39:3-39:5: error: unexpected token 'φ'; expected identifier  |
| `Phys.fluctuation_dissipation` | fail | admin | `8e14f9e24634c760` | -:82:2-82:6: error: `ring_nf` made no progress on the goal  |
| `Phys.hellmann_feynman` | fail | chris | `eb86d5ffac0d745f` | -:67:4-67:40: error: Type mismatch: After simplification, term   this  has type   @HasDerivAt ℝ DenselyNormedField.toNontriviallyNormedField ℂ instCommCStarAlgebraComplex.toCStarA… |
| `Phys.virial_theorem` | fail | admin | `7c536e3a5b972d6e` | -:89:26-89:27: error(lean.synthInstanceFailed): failed to synthesize instance of type class   OfNat (AddCommGroup ℝ) 2 numerals are polymorphic in Lean, but the numeral `2` cannot… |
| `principal_pair_count` | fail | chris | `fcd9a323e18e9abd` | -:53:3-53:5: error: unexpected token 'φ'; expected identifier  |
| `problem_normal_0001` | indeterminate | admin | `` | no hash/environment/diagnostic recorded |
| `QI.apply_eq_sum_choi` | fail | chris | `4c78d9b0e1e57b39` | -:139:2-139:36: error: Type mismatch: After simplification, term   h2  has type   @Matrix.PosSemidef (n × m) ℂ Complex.instRing Complex.partialOrder Complex.instStarRing     ((QI.… |
| `QI.bellState_normalized` | fail | admin | `abe9d6a6244fd7df` | -:26:32-26:55: error: Function expected at   SchmidtDecomp but this term has type   ?m.1  Note: Expected a function because this term is being applied to the argument   bellState … |
| `QI.classical_query_lower_bound_rpow` | fail | chris | `eee185857cad4349` | -:44:56-44:64: error(lean.unknownIdentifier): Unknown identifier `QueryAlg`  Note: It is not possible to treat `QueryAlg` as an implicitly bound variable here because the `autoImp… |
| `QI.data_processing` | fail | chris | `f825fb25912ee6f9` | -:148:10-148:29: error(lean.unknownIdentifier): Unknown identifier `trace_mul_re_nonneg`  |
| `QI.hardy_paradox` | fail | admin | `2bd35eee349922e7` | -:106:9-106:10: error: a universe level named `u` has already been declared  |
| `QI.hasDerivAt_logAnti` | fail | admin | `53cb8bcee1aa5829` | -:130:4-130:8: error(lean.unknownIdentifier): Unknown identifier `Rval`  Note: It is not possible to treat `Rval` as an implicitly bound variable here because the `autoImplicit` o… |
| `QI.hasDerivAt_neg_inv` | fail | chris | `704d88ff07629b36` | -:42:2-42:12: error: `field_simp` made no progress on the goal  |
| `QI.holevo_bound` | fail | admin | `2c58825063f9b18e` | -:290:8-290:26: error: `simp` made no progress  |
| `QI.isContraction_iff` | fail | admin | `2d7dcff86bc18470` | -:110:28-110:65: error: Type mismatch: After simplification, term   (Unitary.mem_iff.mp hU).left  has type   @Eq (Matrix q q ℂ) (star U * U) 1 but is expected to have type   @Eq (… |
| `QI.isSelfAdjoint_conj` | fail | chris | `aacfc8a1fee8ea86` | -:544:66-545:4: error: unexpected token 'omit'; expected 'lemma'  |
| `QI.jointlyDiagonalizable_of_commute` | fail | admin | `b8ac3c999309335f` | -:20:4-20:27: error: Function expected at   JointlyDiagonalizable but this term has type   ?m.1  Note: Expected a function because this term is being applied to the argument   ρ  … |
| `QI.simon_algorithm` | fail | admin | `ff5cf74ffd7ccc43` | -:50:20-50:21: error(lean.unknownIdentifier): Unknown identifier `V`  Note: It is not possible to treat `V` as an implicitly bound variable here because the `autoImplicit` option … |
| `QI.steane_code` | fail | chris | `91bdbe3214fec713` | -:107:2-107:8: error: Tactic `decide` failed for proposition   (if 0 + 0 = 0 then 1 else -1) = if 0 = 0 then if 0 = 0 then 1 else -1 else -if 0 = 0 then 1 else -1 because its `Dec… |
| `QPhys.bcH_special` | fail | admin | `bc9164343dfaf5a9` | -:111:6-111:47: error: Type mismatch: After simplification, term   HasDerivAt.scomp s h₁ h₂  has type   @HasDerivAt ℝ DenselyNormedField.toNontriviallyNormedField 𝔸 NonUnitalNorm… |
| `QPhys.canonical_commutator` | fail | chris | `beab8f810538557e` | -:61:4-61:53: error: Type mismatch: After simplification, term   ContinuousLinearMap.hasDerivAt Complex.ofRealCLM  has type   @HasDerivAt ℝ DenselyNormedField.toNontriviallyNormed… |
| `QPhys.commuting_simultaneous` | fail | chris | `49695fbd4d2212e7` | -:70:4-70:7: error: No goals to be solved  |
| `QPhys.ehrenfest` | fail | chris | `37a5404e701d24d9` | -:41:2-41:37: error: Type mismatch: After simplification, term   HasFDerivAt.comp_hasDerivAt t hL hA  has type   @HasDerivAt ℝ DenselyNormedField.toNontriviallyNormedField (E →L[ℝ… |
| `QPhys.oscillator_spectrum` | fail | admin | `083778ed264bac62` | -:176:27-176:48: error: Function expected at   LadderSystem but this term has type   ?m.1  Note: Expected a function because this term is being applied to the argument   (ℕ →₀ ℂ) … |
| `QPhys.particle_in_box` | fail | chris | `451fe26d1aa37c17` | -:57:6-57:33: error: Type mismatch: After simplification, term   HasDerivAt.pow (hf' t) 2  has type   @HasDerivAt ℝ DenselyNormedField.toNontriviallyNormedField ℝ Real.normedCommR… |
| `QPhys.spectral_theorem_finite` | fail | admin | `9afd920aaf47e26d` | -:63:4-63:37: error: Type mismatch: After simplification, term   h  has type   @Eq (Matrix n n 𝕜) A     (((↑hA.eigenvectorUnitary : Matrix n n 𝕜) * Matrix.diagonal fun (x : n) =… |
| `QPhys.stone_generator` | fail | chris | `c7f9d6f7cafe5db7` | -:104:10-104:68: error: Type mismatch: After simplification, term   HasDerivAt.add (DifferentiableAt.hasDerivAt hx) (DifferentiableAt.hasDerivAt hy)  has type   @HasDerivAt ℝ Dens… |
| `ray_cover` | fail | chris | `adcab2c13e7bb4f2` | -:78:10-78:11: error: Tactic `introN` failed: There are no additional binders or `let` bindings in the goal to introduce  p : ℕ inst✝ : Fact (Nat.Prime p) ⊢ Std.Symm (cycleAdj p)  |
| `ray_unique_factorization` | fail | chris | `f13a61a4cfe98c66` | -:133:46-133:53: error: Tactic `assumption` failed  case h.zero hj : 0 < 4 ⊢ rotate ⟨(↑⟨0, hj⟩ + 3) % 4, ⋯⟩ = ⟨0, hj⟩  |
| `ray_zero_singularity` | fail | chris | `4e13e1e289c09a30` | -:61:14-63:26: error: unsolved goals j : ActiveRay h_active_ray : ∀ (j : Fin 4), ↑j + 1 < 5 ⊢ q = 5  |
| `Ray.card` | fail | chris | `832af91f0c1ec207` | -:151:3-151:5: error: unexpected token 'φ'; expected identifier  |
| `Ray.toNat_E` | fail | chris | `8746d105be205d18` | -:231:6-232:47: error: unsolved goals case mp.A.B g : ℕ hg : g % 5 = 1 ⊢ (Ray.A, Ray.B) ∈ {(Ray.A, Ray.B), (Ray.B, Ray.C), (Ray.C, Ray.D)}  case mp.B.C g : ℕ hg : g % 5 = 1 ⊢ (Ray… |
| `residue_injective` | fail | chris | `d2a153eadbb41b7a` | -:234:17-234:19: error: unexpected token 'φ'; expected identifier  |
| `rotate_order_4` | fail | chris | `665a423a1716d200` | -:42:3-42:5: error: unexpected token 'φ'; expected identifier  |
| `rotation_is_complex_mul` | fail | chris | `d0074e7d25eb20c0` | -:271:10-271:16: error: `exact?` could not close the goal. Try `apply?` to see partial suggestions.  |
| `sigma_of_prime` | fail | chris | `c0c96c55eccb877c` | -:175:7-175:52: error: Type mismatch: After simplification, term   congr_arg Fin.val h  has type   @Eq ℕ (↑(ray p)) 0 but is expected to have type   @Eq ℕ (p % 5) 0  |
| `spiral_phase_security` | fail | chris | `879bdbbd92cf29c0` | -:50:3-50:5: error: unexpected token 'φ'; expected identifier  |
| `spiralPrime_norm` | fail | chris | `c566d13b6e01413d` | -:41:11-41:13: error: unexpected token 'φ'; expected identifier  |
| `submission` | fail | admin | `e963c93f7c958e5e` | -:12:2-12:7: error: `grind` failed case grind G : Type inst : Magma G h : ∀ (x y z w : G), x = y ◇ (x ◇ y) ◇ z ◇ w x y z w : G h_1 : ¬x = y ◇ (x ◇ z) ◇ (y ◇ w) ⊢ False [grind] Goa… |
| `test` | fail | admin | `6b1d5c017d01975e` | -:33:2-33:7: error: `grind` failed case grind G : Type u_1 inst : Magma G h : ∀ (x y z w : G), x = y ◇ (z ◇ (x ◇ x) ◇ w) x y z w : G h1 : x = y ◇ (z ◇ (x ◇ x) ◇ w) h2 : y = x ◇ (z… |
| `twin_prime_case` | fail | chris | `34c963d7064cbfdd` | -:75:3-75:5: error: unexpected token 'φ'; expected identifier  |
| `unique_membership` | fail | chris | `ca438e1652eff6f1` | -:91:3-91:5: error: unexpected token 'φ'; expected identifier  |
| `UnitaryRep.preserves_inner` | fail | chris | `8ae40aff1f56f267` | -:51:20-51:21: error: Application type mismatch: The argument   ℂ has type   Type but is expected to have type   ?m.4 →+* ?m.5 in the application   LinearPMap ℂ  |
| `universal_admissibility_count` | fail | chris | `947f81a31a33e467` | -:78:6-78:12: error: found a proof, but the corresponding tactic failed:   (expose_names; exact (ZMod.val_ne_zero ↑g).mp hg)  It may be possible to correct this proof by adding ty… |
| `Zeta23Redux.LinAlg.weyl_posIndexAbove` | fail | admin | `04344e93b92fdb43` | -:172:4-172:90: error: Type mismatch: After simplification, term   LinearIndependent.comp this (fun i => ↑i) Subtype.val_injective  has type   @LinearIndependent ↥s ℂ (EuclideanSp… |
| `Zeta23Scaffold.integral_sinc_fourth` | fail | admin | `e86cfc18efe27d6e` | -:34:4-34:14: error: `field_simp` made no progress on the goal  |
| `Zeta23Scaffold.integral_sinc_sq` | fail | chris | `5aeb1f0cd35e8f91` | -:39:4-39:51: error: Type mismatch: After simplification, term   HasDerivAt.neg (HasDerivAt.mul_const (hasDerivAt_id t) x)  has type   @HasDerivAt ℝ DenselyNormedField.toNontrivia… |
