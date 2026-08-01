# Mathlib PR Blueprints

Date: 2026-08-01

Scope: extraction plan for turning `docs/MATHLIB-UPSTREAM-CANDIDATES.md` into
Mathlib-sized pull requests. This is a planning document, not a claim that the
local declarations can be copied verbatim. Each batch below names the local proof
payload, the current imports/dependencies, the Mathlib-facing statement shape,
and the project-specific material that must be removed or generalized.

Hard boundary: do not upstream Brockian narrative claims, RH/Goldbach schemas,
prime-distribution claims, registry machinery, or project-specific target
containers. The payload here is reusable operator theory, finite counting,
finite Fourier analysis, and elementary analytic infrastructure.

## Extraction Rules

- One PR should expose one reusable API layer. Avoid "Weyl campaign" bundles.
- Replace `import Mathlib` with focused Mathlib imports before opening a PR.
- Keep local namespaces out of upstream statements. Candidate targets should live
  under existing namespaces such as `LinearPMap`, `ContinuousLinearMap`,
  `Finset`, `ZMod`, `SimpleGraph`, or a narrow new Mathlib namespace.
- Prefer theorem statements over project definitions when the project definition
  is only a wrapper around an existing Mathlib concept.
- Generalize from `Fin 5` and `DihedralGroup 5` before PR unless the exact `5`
  statement is the mathematical object being contributed as an example.
- Preserve the proof payload, but expect renaming, import minimization, and
  statement refactoring.

## Current Source Imports

The upstream candidates currently use broad imports. These are the exact source
headers observed in the repo:

| Local file | Current imports | Upstream replacement direction |
| --- | --- | --- |
| `Brockian/WeylOperator.lean` | `Mathlib` | Focus `LinearPMap`, adjoint, complex inner-product spaces, norm/inner lemmas |
| `Brockian/WeylCayley.lean` | `Mathlib`, `Brockian.WeylOperator` | Depends on PR 1; add submodule orthogonal/dense-range imports |
| `Brockian/WeylClosure.lean` | `Mathlib`, `Brockian.WeylOperator` | Depends on PR 1; add `LinearPMap.closure`, closed graph, topology imports |
| `Brockian/WeylEssSelfAdjoint.lean` | `Brockian.WeylOperator` | Depends on PRs 1 and 3/4; add `ContinuousLinearMap` self-adjoint imports |
| `Brockian/WeylFreeLaplacian2.lean` | `Mathlib`, `Brockian.WeylCayley`, `Brockian.WeylEssSelfAdjoint`, `Brockian.WeylFreeLaplacian` | Only extract unitary-transfer and finite multiplication fragments after PRs 2-5 |
| `Brockian/Admissibility.lean` | `Mathlib` | Focus `ZMod`, `Finset.card`, complements |
| `Brockian/AdmissibilityCRT.lean` | `Mathlib`, `Brockian.Admissibility` | Depends on PR 9; focus `ZMod.chineseRemainder`, product finsets |
| `Brockian/Sieve.lean` | `Mathlib` | Only extract `TwinAdmissibleAt` cardinality-style finite facts |
| `Brockian/SingularSeries.lean` | `Mathlib` | Do not upstream current infinite-product definition as-is |
| `Brockian/SingularSeriesConvergence.lean` | `Mathlib`, `Brockian.SingularSeries` | Depends on redesigned local-factor API |
| `Brockian/Automorphism*.lean` | `Mathlib`, `Brockian.Automorphism` | Focus graph isomorphisms, cycle automorphisms, dihedral action |
| `Brockian/D5*.lean` | `Mathlib`, local D5 modules | Generalize from `5` to finite cyclic Fourier/cycle graph where feasible |
| `Brockian/Spectral.lean`, `Brockian/CycleSpectrumFamily.lean`, `Brockian/C5SpectralMultiplicities.lean` | `Mathlib`, local spectral/connectivity files | Connect to graph/matrix operator API before upstream |

Use `scripts/list_upstream_decls.py` to refresh this inventory.

## Dependency Spine

1. `LinearPMap.IsSymmetric` predicate and elementary facts.
2. Shifted range API and symmetric non-real estimates.
3. Adjoint orthogonality and deficiency-space dense-range criteria.
4. Closure/closability facts for symmetric `LinearPMap`s.
5. Full-domain bounded self-adjoint examples and unitary transfer.
6. Finite `ZMod` counting and CRT product-cardinality lemmas.
7. Singular-series local finite factors and convergence tails.
8. Cyclic graph automorphisms, Fourier/projector algebra, and cycle spectra.

This order lets each PR import only previous Mathlib layers, not Brockian files.

## PR 1: `LinearPMap.IsSymmetric` Core API

Local payload:

- `Brockian.Weyl.Operator.IsSymmetric`
- `Brockian.Weyl.Operator.IsSymmetric.inner_apply`
- `Brockian.Weyl.Operator.IsSymmetric.inner_self_im`
- `Brockian.Weyl.Operator.IsSymmetric.im_eq_zero_of_apply_eq_smul`
- `Brockian.Weyl.Operator.IsSymmetric.eq_zero_of_apply_eq_smul`

Current source/imports:

- File: `Brockian/WeylOperator.lean`
- Current import: `Mathlib`
- Local namespace: `Brockian.Weyl.Operator`

Proposed Mathlib target:

- Namespace: `LinearPMap`
- Predicate: `LinearPMap.IsSymmetric (T : E →ₗ.[K] E) : Prop`
- Primary complex version first:
  `T.IsSymmetric -> T v = z • v -> Complex.im z != 0 -> v = 0`
- If existing `RCLike` lemmas make it low-cost, generalize the real-form facts to
  `RCLike K`; keep non-real spectral statements complex-specific.

Project-specific cleanup:

- Replace `Brockian.Weyl.Operator.IsSymmetric` with `LinearPMap.IsSymmetric`.
- Drop scalar-multiplication example lemmas such as `smulPMap_isSymmetric` from
  this PR unless they are needed as tests.
- Rename `inner_apply` to follow existing adjoint/formal-adjoint conventions.

Acceptance test before PR:

- A local extraction file should import only focused `LinearPMap` and inner
  product modules, not `Mathlib`.

## PR 2: Symmetric Non-Real Resolvent Estimate

Local payload:

- `Brockian.Weyl.Operator.IsSymmetric.norm_sub_smul_ge`
- `Brockian.Weyl.Cayley.norm_add_I_smul_eq`
- `Brockian.Weyl.Cayley.apply_ne_I_smul`
- `Brockian.Weyl.Cayley.apply_ne_neg_I_smul`

Current source/imports:

- Files: `Brockian/WeylOperator.lean`, `Brockian/WeylCayley.lean`
- Current imports: `Mathlib`, then local `Brockian.WeylOperator`
- Depends on PR 1.

Proposed Mathlib target:

- Namespace: `LinearPMap.IsSymmetric`
- Core theorem:
  `|Complex.im z| * ||v|| <= ||T v - z • v||`
  for `v : T.domain`.
- Cayley corollary:
  `||T v + Complex.I • v|| = ||T v - Complex.I • v||`.

Project-specific cleanup:

- Remove Cayley/Weyl names from the estimate.
- Consider exposing a squared-norm identity if it makes the inequality proof
  cleaner and more useful.
- Keep sign conventions aligned with Mathlib's inner-product linearity.

## PR 3: Shifted Range API for `LinearPMap`

Local payload:

- `Brockian.Weyl.Cayley.rangeSMulSub`
- `Brockian.Weyl.Cayley.mem_rangeSMulSub`
- `Brockian.Weyl.Cayley.rangeAddI`
- `Brockian.Weyl.Cayley.rangeSubI`

Current source/imports:

- File: `Brockian/WeylCayley.lean`
- Current imports: `Mathlib`, `Brockian.WeylOperator`
- Depends on PR 1; PR 2 is useful but not logically required.

Proposed Mathlib target:

- Namespace: `LinearPMap`
- Name shape: `LinearPMap.rangeSubSMul` or
  `LinearPMap.range_smul_sub`.
- Membership theorem:
  `u ∈ T.rangeSubSMul w ↔ ∃ v : T.domain, T v - w • (v : H) = u`.

Project-specific cleanup:

- Generalize scalar field where possible; the construction itself is not
  complex-specific.
- If Mathlib has a preferred range-of-map API, state this as an image/range
  theorem instead of introducing an unnecessary new definition.

## PR 4: Adjoint Orthogonality Equals Deficiency Data

Local payload:

- `Brockian.Weyl.Operator.deficiencySpace`
- `Brockian.Weyl.Operator.mem_deficiencySpace_iff`
- `Brockian.Weyl.Cayley.mem_orthogonal_rangeSMulSub_iff`

Current source/imports:

- Files: `Brockian/WeylOperator.lean`, `Brockian/WeylCayley.lean`
- Depends on PRs 1 and 3.

Proposed Mathlib target:

- Namespace: `LinearPMap`
- Preferred statement as a submodule equality if practical:
  `(T.rangeSubSMul (star z)).orthogonal = T.adjoint.deficiencySpace z`
- Keep an iff theorem as the convenient user-facing corollary.

Project-specific cleanup:

- Replace "Weyl" and "Cayley" wording with adjoint/range terminology.
- Audit conjugation orientation explicitly. The current local theorem is the
  identity behind `ker(T* - z) = ran(T - conj z)^\perp`.
- If the exact equality is awkward, PR the membership iff first.

## PR 5: Deficiency Triviality and Dense Shifted Ranges

Local payload:

- `Brockian.Weyl.Cayley.deficiencySpace_eq_bot_iff`
- `Brockian.Weyl.Operator.EssentiallySelfAdjoint`
- `Brockian.Weyl.Cayley.essentiallySelfAdjoint_iff`

Current source/imports:

- Files: `Brockian/WeylOperator.lean`, `Brockian/WeylCayley.lean`
- Depends on PRs 1, 3, and 4.

Proposed Mathlib target:

- First theorem:
  `T.deficiencySpace z = ⊥ ↔ Dense (T.rangeSubSMul (star z) : Set H)`.
- Later predicate:
  `LinearPMap.EssentiallySelfAdjoint T`, if maintainers accept this API layer.
- Range-density criterion at `+I` and `-I` as a theorem about that predicate.

Project-specific cleanup:

- Do not mention "Gate 1", Weyl, RH, or Brockian operators.
- If maintainers object to adding `EssentiallySelfAdjoint`, land the deficiency
  dense-range theorem independently and leave the predicate local.

## PR 6: Closure and Closability of Symmetric `LinearPMap`s

Local payload:

- `Brockian.Weyl.Closure.inner_adjoint_left`
- `Brockian.Weyl.Closure.symmetric_le_adjoint`
- `Brockian.Weyl.Closure.symmetric_domain_le_adjoint_domain`
- `Brockian.Weyl.Closure.symmetric_adjoint_eq`
- `Brockian.Weyl.Closure.adjoint_isClosed'`
- `Brockian.Weyl.Closure.symmetric_isClosable`
- `Brockian.Weyl.Closure.symmetric_closure_le_adjoint`
- `Brockian.Weyl.Closure.closure_eq_self_of_isClosed`
- `Brockian.Weyl.Closure.deficiencySet`
- `Brockian.Weyl.Closure.mem_deficiencySet_iff_mem_deficiencySpace`
- `Brockian.Weyl.Closure.isClosed_deficiencySet`

Current source/imports:

- File: `Brockian/WeylClosure.lean`
- Current imports: `Mathlib`, `Brockian.WeylOperator`
- Depends on PRs 1 and 4.

Proposed Mathlib target:

- Namespace: `LinearPMap`
- Split if needed:
  - PR 6a: symmetric inclusion `T <= T.adjoint` and closability.
  - PR 6b: deficiency spaces are closed.

Project-specific cleanup:

- Determine which local declarations are aliases of existing Mathlib facts.
- Prefer submodule-level deficiency-space closure over a parallel set wrapper.

## PR 7: Full-Domain Bounded Self-Adjoint Operators Are ESA

Local payload:

- `Brockian.Weyl.ESA.clm_domain`
- `Brockian.Weyl.ESA.clm_dense`
- `Brockian.Weyl.ESA.clm_isSymmetric`
- `Brockian.Weyl.ESA.vec_eq_zero_of_inner`
- `Brockian.Weyl.ESA.clm_deficiency_eq_bot`
- `Brockian.Weyl.ESA.clm_essentiallySelfAdjoint`
- Optional example: `Brockian.Weyl.ESA.id_essentiallySelfAdjoint`

Current source/imports:

- File: `Brockian/WeylEssSelfAdjoint.lean`
- Current import: `Brockian.WeylOperator`
- Depends on PRs 1 and 5.

Proposed Mathlib target:

- Namespace: `ContinuousLinearMap` or `LinearPMap`
- Statement:
  `IsSelfAdjoint A -> LinearPMap.EssentiallySelfAdjoint (A.toPMap ⊤)`.

Project-specific cleanup:

- Omit the identity example unless requested as a doc-test style example.
- Replace direct deficiency proof with PR 5 criterion if it shortens the proof.

## PR 8: ESA Transfer Across Unitary Equivalence

Local payload:

- `Brockian.Weyl.FreeLaplacian2.dense_map_iff`
- `Brockian.Weyl.FreeLaplacian2.rangeSMulSub_image`
- `Brockian.Weyl.FreeLaplacian2.essentiallySelfAdjoint_transfer`
- `Brockian.Weyl.FreeLaplacian2.conjCLM_toPMap_essentiallySelfAdjoint_iff`
- `Brockian.Weyl.FreeLaplacian2.conjCLM_essentiallySelfAdjoint`

Current source/imports:

- File: `Brockian/WeylFreeLaplacian2.lean`
- Current imports: `Mathlib`, `Brockian.WeylCayley`,
  `Brockian.WeylEssSelfAdjoint`, `Brockian.WeylFreeLaplacian`
- Depends on PRs 3, 5, and 7.

Proposed Mathlib target:

- Namespace: `LinearIsometryEquiv` plus corollaries in `LinearPMap`.
- Use a bundled conjugacy relation if Mathlib already has one; otherwise use
  explicit domain/action hypotheses as in the local proof.

Project-specific cleanup:

- Do not upstream `freeLaplacian_essentiallySelfAdjoint_of_fourier` here.
- Separate the finite multiplication example from the unitary-transfer theorem.

## PR 9: Finite `ZMod` Exclusion Counts

Local payload:

- `Brockian.Admissibility.admissibleResidues`
- `Brockian.Admissibility.universal_admissibility_count`
- `Brockian.Admissibility.admissibility_count_three`
- `Brockian.Admissibility.admissibility_count_five`
- `Brockian.Sieve.TwinAdmissibleAt`
- `Brockian.Sieve.twin_admissible_card`

Current source/imports:

- Files: `Brockian/Admissibility.lean`, `Brockian/Sieve.lean`
- Current import: `Mathlib`

Proposed Mathlib target:

- Namespace: `ZMod` or `Finset`
- General lemma: for a finite additive group and `g != 0`, the complement of
  `{0, -g}` has cardinality `q - 2` when the two excluded points are distinct.
- Specialize to `ZMod q` with prime or `2 < q` hypotheses only where needed.

Project-specific cleanup:

- Remove "admissible" and "twin prime" naming from the primary theorem.
- Keep `TwinAdmissibleAt` as a downstream local wrapper, not as Mathlib API.

## PR 10: CRT Product Cardinalities

Local payload:

- `Brockian.Admissibility.CRT.admissibleResidues_crt_card`
- `Brockian.Admissibility.CRT.admissibleResidues_crt_card_two_primes`
- Optional example: `Brockian.Admissibility.CRT.admissible_count_three_five`

Current source/imports:

- File: `Brockian/AdmissibilityCRT.lean`
- Current imports: `Mathlib`, `Brockian.Admissibility`
- Depends on PR 9 if the exclusion-count definitions are upstreamed.

Proposed Mathlib target:

- First a generic theorem:
  for an equivalence `e : A ≃ B × C`, the cardinality of elements satisfying
  `P (e x).1 ∧ Q (e x).2` is `card P * card Q`.
- Then a `ZMod.chineseRemainder` corollary.

Project-specific cleanup:

- Do not mention primes except in the `ZMod.chineseRemainder` specialization.
- Make the example for moduli `3` and `5` a test/example, not the main theorem.

## PR 11: Singular-Series Finite Local Factors

Local payload:

- `Brockian.SingularSeries.nu_p`
- `Brockian.SingularSeries.nu_p_eq_image_card`
- `Brockian.SingularSeries.nu_p_lt_p_of_admissible`
- `Brockian.SingularSeries.localFactor`
- `Brockian.SingularSeries.localFactorAt`
- `Brockian.SingularSeries.localFactorAt_eq`
- `Brockian.SingularSeries.localFactorAt_of_not_prime`
- `Brockian.SingularSeries.local_factor_denom_ne_zero`
- `Brockian.SingularSeries.local_factor_pos`
- `Brockian.SingularSeries.localFactorAt_pos`
- `Brockian.SingularSeries.singular_series_finite_pos`
- `Brockian.SingularSeries.Convergence.nu_p_eq_card_of_lt`

Current source/imports:

- Files: `Brockian/SingularSeries.lean`,
  `Brockian/SingularSeriesConvergence.lean`
- Current imports: `Mathlib`, then local `Brockian.SingularSeries`

Proposed Mathlib target:

- Namespace: likely a new number-theory file only after maintainer discussion.
- Do not introduce `singularSeries` as a fallback-to-zero limit.
- Upstream the finite residue count and finite product positivity first.

Project-specific cleanup:

- Rename away from Hardy-Littlewood tuple language unless Mathlib accepts a
  singular-series namespace.
- Generalize `nu_p_eq_card_of_lt`: primality is not needed; it is a finite
  `Nat.mod` injectivity lemma.

## PR 12: Singular-Series Tail Convergence

Local payload:

- `Brockian.SingularSeries.Convergence.err_bound`
- `Brockian.SingularSeries.Convergence.localFactor_sub_one_bound`
- `Brockian.SingularSeries.Convergence.summable_localFactorAt_sub_one`
- `Brockian.SingularSeries.Convergence.singularSeriesFinite_tendsto_pos`
- `Brockian.SingularSeries.Convergence.singular_series_pos'`

Current source/imports:

- File: `Brockian/SingularSeriesConvergence.lean`
- Depends on PR 11 and a Mathlib-compatible infinite-product design.

Proposed Mathlib target:

- Split `err_bound` into an elementary analysis PR if it is not already present.
- State convergence using `Multipliable`/`tprod` or whatever Mathlib's product
  API maintainers prefer.

Project-specific cleanup:

- Avoid any phrasing that implies Hardy-Littlewood asymptotics or prime
  distribution consequences.
- Replace local `singularSeries` definition before this PR is attempted.

## PR 13: Cycle Graph Automorphisms and `Aut(C_n) ~= D_n`

Local payload:

- `Brockian.Automorphism.rot_map_adj`
- `Brockian.Automorphism.refl_map_adj`
- `Brockian.Automorphism.dihedral_action_faithful`
- `Brockian.Automorphism.Full.dihedralHom_surjective`
- `Brockian.Automorphism.Full.dihedralHom_bijective`
- `Brockian.Automorphism.Full.aut_equiv_dihedral`
- `Brockian.Automorphism.Full.aut_card_eq_ten`

Current source/imports:

- Files: `Brockian/Automorphism.lean`, `Brockian/AutomorphismFull.lean`
- Current imports: `Mathlib`, then local `Brockian.Automorphism`

Proposed Mathlib target:

- General theorem for `SimpleGraph.cycleGraph n` with suitable hypotheses,
  probably `3 <= n`.
- Equivalence:
  `DihedralGroup n ≃* (SimpleGraph.cycleGraph n ≃g SimpleGraph.cycleGraph n)`.

Project-specific cleanup:

- Do not upstream `C5` as the main object.
- Rework enumeration-style `Fin 5` cases into structural cycle-graph arguments.

## PR 14: Finite Cyclic Fourier Orthogonality and Projectors

Local payload:

- `Brockian.D5Isotypic.omega_isPrimitiveRoot`
- `Brockian.D5Isotypic.omega_pow_modEq`
- `Brockian.D5Isotypic.omegaPow_add`
- `Brockian.D5Isotypic.omegaPow_neg`
- `Brockian.D5Isotypic.omega_pow_eq_one_iff`
- `Brockian.D5Isotypic.sum_omegaPow`
- `Brockian.D5Isotypic.character_orthogonality`
- `Brockian.D5Isotypic.isotypicProjector_eigenmode`
- `Brockian.D5FourierInversion.sum_isotypicProjectors`
- `Brockian.D5FourierInversion.fourier_inversion`
- `Brockian.D5FourierInversion.isotypicProjector_idempotent`
- `Brockian.D5FourierInversion.isotypicProjector_orthogonal`

Current source/imports:

- Files: `Brockian/D5Isotypic.lean`,
  `Brockian/D5FourierInversion.lean`
- Current imports: `Mathlib`, local D5 representation modules
- Depends naturally on PR 13 only for graph-action packaging, not for pure
  Fourier orthogonality.

Proposed Mathlib target:

- Namespace: finite cyclic characters or `ZMod`.
- Generalize `Fin 5` to `ZMod n` or a finite cyclic group with a primitive root
  of unity.
- Projectors should be stated as Fourier idempotents on `ZMod n -> C`.

Project-specific cleanup:

- Remove D5 language from the pure cyclic Fourier results.
- Keep cycle-graph representation invariance as a later application.

## PR 15: Cycle Adjacency and Laplacian Eigenmodes

Local payload:

- `Brockian.D5LaplacianModes.adjacency_apply`
- `Brockian.D5LaplacianModes.adjacency_eq_pullbacks`
- `Brockian.D5LaplacianModes.adjacency_eigenmode`
- `Brockian.D5LaplacianModes.adjacency_eigenmode_cos`
- `Brockian.D5LaplacianModes.laplacian_apply`
- `Brockian.D5LaplacianModes.laplacian_eigenmode`
- `Brockian.CycleSpectrumFamily.mem_cycleSpectrum`
- `Brockian.CycleSpectrumFamily.lambda_max_cycle`
- `Brockian.CycleSpectrumFamily.laplacianCycleSpectrum_nonneg`
- `Brockian.CycleSpectrumFamily.algebraic_connectivity_pos`

Current source/imports:

- Files: `Brockian/D5LaplacianModes.lean`,
  `Brockian/CycleSpectrumFamily.lean`, `Brockian/Spectral.lean`
- Current imports: `Mathlib`, local representation/spectral files
- Depends on PR 14 for Fourier eigenmodes.

Proposed Mathlib target:

- Connect to an actual adjacency operator or matrix for
  `SimpleGraph.cycleGraph n`.
- State eigenvalues as `2 * Real.cos (2 * pi * k / n)` for adjacency and
  `2 - 2 * Real.cos (2 * pi * k / n)` for graph Laplacian.

Project-specific cleanup:

- Treat C5/golden ratio facts as examples after the general cycle theorem.
- Do not upstream "golden uniqueness" as a standalone theorem.

## PR 16: C5 Multiplicity Examples

Local payload:

- `Brockian.C5SpectralMultiplicities.c5SpectrumMultiset_eq`
- `Brockian.C5SpectralMultiplicities.multiplicity_two`
- `Brockian.C5SpectralMultiplicities.multiplicity_golden_sub_one`
- `Brockian.C5SpectralMultiplicities.multiplicity_neg_golden`
- `Brockian.C5SpectralMultiplicities.c5LaplacianMultiset_eq`
- `Brockian.C5SpectralMultiplicities.multiplicity_lap_zero`
- `Brockian.C5SpectralMultiplicities.multiplicity_lap_gap`
- `Brockian.C5SpectralMultiplicities.multiplicity_lap_large`

Current source/imports:

- File: `Brockian/C5SpectralMultiplicities.lean`
- Current imports: `Mathlib`, `Brockian.Spectral`, `Brockian.Connectivity`,
  `Brockian.CycleSpectrumFamily`
- Depends on PR 15.

Proposed Mathlib target:

- Prefer a general multiplicity theorem for `C_n`: modes `k` and `n-k` share
  eigenvalues, with special cases at `0` and `n/2` when even.
- C5 can be a test/example, not first-class API.

Project-specific cleanup:

- Remove Brockian framing around "golden" numerology.
- Avoid this PR until the general cycle-spectrum API exists.

## First Five Recommended PRs

1. PR 1: `LinearPMap.IsSymmetric` core API.
2. PR 2: symmetric non-real resolvent estimate and Cayley norm identity.
3. PR 3: shifted range API for `LinearPMap`.
4. PR 4: adjoint orthogonality equals deficiency data.
5. PR 5: deficiency triviality iff shifted range dense, with the ESA predicate
   only if maintainers accept that API layer.

These five form the cleanest Mathlib contribution path because each is general,
operator-theoretic, and independent of Brockian arithmetic narratives. They also
turn the strongest local proof payload into a coherent upstream ladder.

## Script Support

`scripts/list_upstream_decls.py` is a read-only inventory helper. It performs a
lightweight scan of the current candidate files and prints imports, namespaces,
and top-level declarations. It is intentionally not a Lean parser and should be
used for planning only.

Example:

```bash
python3 scripts/list_upstream_decls.py
python3 scripts/list_upstream_decls.py Brockian/WeylOperator.lean
python3 scripts/list_upstream_decls.py --names-only Brockian/WeylCayley.lean
```
