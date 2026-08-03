# Mathlib Upstream Candidates

Date: 2026-08-01

Scope: documentation-only triage of the current `Brockian` Lean codebase. This is
not a claim that these declarations are ready to PR as-is. It identifies reusable
mathematical content, exact local module/declaration names, and the cleanup or
generalization needed before Mathlib submission.

Boundary: this list is infrastructure only. It does not claim progress on RH,
Goldbach, Hilbert-Polya, equidistribution, or Hardy-Littlewood conjectures. The
number-theory candidates below are finite counting or convergence infrastructure,
not prime-distribution theorems.

## Selection Criteria

- The declaration proves a reusable mathematical lemma, not a Brockian narrative
  claim.
- The statement is plausibly useful outside this repo, especially for Mathlib's
  `LinearPMap`, Hilbert-space operator theory, finite cyclic Fourier analysis,
  `ZMod`/CRT counting, and elementary singular-series infrastructure.
- The cleanup path is concrete: rename, reduce imports, remove project-specific
  packaging, or generalize from `5` to an arbitrary finite cyclic group/cycle.

## Highest-Value Candidates

### 1. `LinearPMap` symmetric-operator API

Local module: `Brockian.WeylOperator`

Local declarations:

- `Brockian.Weyl.Operator.IsSymmetric`
- `Brockian.Weyl.Operator.IsSymmetric.inner_apply`
- `Brockian.Weyl.Operator.IsSymmetric.inner_self_im`
- `Brockian.Weyl.Operator.IsSymmetric.im_eq_zero_of_apply_eq_smul`

Why generally useful: Mathlib has `LinearPMap.IsFormalAdjoint` and adjoints, but
this repo builds the missing convenient predicate and first facts for symmetric
partially-defined operators. The real-quadratic-form and real-eigenvalue lemmas
are standard Hilbert-space operator theory and are broadly useful for unbounded
operator work.

Cleanup before PR:

- Move to a `LinearPMap`/inner-product-space namespace, likely as
  `LinearPMap.IsSymmetric`.
- Check whether any recent Mathlib API already added overlapping declarations.
- Avoid importing all of `Mathlib`; replace with focused imports.
- Rework theorem names to Mathlib style and add simp/projection lemmas only where
  they will be used downstream.

### 2. Basic non-real resolvent inequality for symmetric `LinearPMap`s

Local module: `Brockian.WeylOperator`

Local declarations:

- `Brockian.Weyl.Operator.IsSymmetric.norm_sub_smul_ge`
- `Brockian.Weyl.Operator.IsSymmetric.eq_zero_of_apply_eq_smul`

Why generally useful: the inequality
`abs (Complex.im z) * norm v <= norm (T v - z smul v)` is the standard core estimate
behind non-real resolvent injectivity for symmetric operators. It is a strong
library lemma because many later facts should depend on this single estimate
rather than redo the inner-product expansion.

Cleanup before PR:

- Decide whether the statement should be over `RCLike` or specifically complex
  Hilbert spaces. The current proof is complex-specific.
- Consider stating a squared-norm identity first, then deriving the inequality.
- Align scalar action and inner-product convention with existing Mathlib lemmas.

### 3. Range submodule of `T - w`

Local module: `Brockian.WeylCayley`

Local declarations:

- `Brockian.Weyl.Cayley.rangeSMulSub`
- `Brockian.Weyl.Cayley.mem_rangeSMulSub`
- `Brockian.Weyl.Cayley.rangeAddI`
- `Brockian.Weyl.Cayley.rangeSubI`

Why generally useful: many unbounded-operator criteria are stated in terms of
the range of `T - z`. A named submodule plus a clean membership lemma would make
the existing `LinearPMap` API easier to use.

Cleanup before PR:

- Make the construction polymorphic in the scalar field where possible.
- Name it in `LinearPMap` style, for example `LinearPMap.rangeSubSMul`.
- Add simp lemmas for full-domain continuous linear maps if they are accepted.

### 4. Orthogonal complement of a shifted range equals adjoint deficiency data

Local module: `Brockian.WeylCayley`

Local declarations:

- `Brockian.Weyl.Cayley.mem_orthogonal_rangeSMulSub_iff`
- Supporting: `Brockian.Weyl.Operator.deficiencySpace`
- Supporting: `Brockian.Weyl.Operator.mem_deficiencySpace_iff`

Why generally useful: this is the von Neumann identity relating
`(range (T - conj z))^orthogonal` to eigenvectors of `T.adjoint` at `z`. It is
one of the most generally useful missing facts for `LinearPMap` adjoint theory.

Cleanup before PR:

- Generalize names away from Cayley/Weyl terminology.
- Decide the target statement shape: set-level orthogonal complement, submodule
  equality, or iff membership. Mathlib may prefer a submodule equality with the
  membership iff as a corollary.
- Audit conjugation orientation and document the inner-product convention.

### 5. Deficiency space trivial iff shifted range dense

Local module: `Brockian.WeylCayley`

Local declarations:

- `Brockian.Weyl.Cayley.deficiencySpace_eq_bot_iff`
- `Brockian.Weyl.Cayley.essentiallySelfAdjoint_iff`
- Supporting: `Brockian.Weyl.Operator.EssentiallySelfAdjoint`

Why generally useful: this is the range-density form of the deficiency-space
criterion. It connects algebraic kernels inside `T.adjoint.domain` to topological
density of shifted ranges in the ambient Hilbert space.

Cleanup before PR:

- Split into one PR for the deficiency/range-density lemma and a later PR for any
  essential-self-adjointness predicate.
- Consider whether Mathlib wants the predicate named `EssentiallySelfAdjoint` at
  the `LinearPMap` level, or whether this should be a theorem about two named
  kernels.
- Minimize local notation and remove project-specific comments.

### 6. Cayley transform norm identity

Local module: `Brockian.WeylCayley`

Local declarations:

- `Brockian.Weyl.Cayley.norm_add_I_smul_eq`
- `Brockian.Weyl.Cayley.apply_ne_I_smul`
- `Brockian.Weyl.Cayley.apply_ne_neg_I_smul`

Why generally useful: the equality `norm (T v + i smul v) = norm (T v - i smul v)` is
the isometric content behind the Cayley transform for symmetric operators. Even
without packaging the transform as a `LinearIsometry`, the norm identity is a
small, reusable theorem.

Cleanup before PR:

- Put the norm identity next to the non-real resolvent inequality.
- Consider a generalized version for `z` with real part zero, or retain the
  `i`/`-i` statements because they match the Cayley transform.
- If a bundled Cayley transform is later introduced, expose this as its
  `map_norm` proof.

### 7. Symmetric operators are contained in their adjoints and are closable

Local module: `Brockian.WeylClosure`

Local declarations:

- `Brockian.Weyl.Closure.inner_adjoint_left`
- `Brockian.Weyl.Closure.symmetric_le_adjoint`
- `Brockian.Weyl.Closure.symmetric_domain_le_adjoint_domain`
- `Brockian.Weyl.Closure.symmetric_adjoint_eq`
- `Brockian.Weyl.Closure.adjoint_isClosed'`
- `Brockian.Weyl.Closure.symmetric_isClosable`
- `Brockian.Weyl.Closure.symmetric_closure_le_adjoint`
- `Brockian.Weyl.Closure.closure_eq_self_of_isClosed`

Why generally useful: these are standard structural facts for densely-defined
symmetric operators. They would fill real gaps in Mathlib's `LinearPMap` operator
theory and support later self-adjointness APIs.

Cleanup before PR:

- Separate re-export lemmas from genuinely new lemmas. For example,
  `inner_adjoint_left` and `adjoint_isClosed'` may be mostly aliases.
- Check whether `closure_eq_self_of_isClosed` belongs in a general
  `LinearPMap.closure` file.
- Avoid bundling many unrelated closure facts into one large PR.

### 8. Deficiency space as a closed subset/subspace of the Hilbert space

Local module: `Brockian.WeylClosure`

Local declarations:

- `Brockian.Weyl.Closure.deficiencySet`
- `Brockian.Weyl.Closure.mem_deficiencySet_iff_mem_deficiencySpace`
- `Brockian.Weyl.Closure.isClosed_deficiencySet`

Why generally useful: deficiency spaces are normally closed subspaces of the
ambient Hilbert space. The current repo has the exact preimage-of-closed-graph
argument using `LinearPMap.adjoint_isClosed`.

Cleanup before PR:

- Prefer a `Submodule` version if possible, not only a `Set` version.
- If Mathlib accepts `deficiencySpace`, make this theorem part of that API rather
  than introduce a second parallel definition.
- Align theorem names with any final deficiency-space naming.

### 9. Full-domain bounded self-adjoint operators are essentially self-adjoint

Local module: `Brockian.WeylEssSelfAdjoint`

Local declarations:

- `Brockian.Weyl.ESA.clm_domain`
- `Brockian.Weyl.ESA.clm_dense`
- `Brockian.Weyl.ESA.clm_isSymmetric`
- `Brockian.Weyl.ESA.vec_eq_zero_of_inner`
- `Brockian.Weyl.ESA.clm_deficiency_eq_bot`
- `Brockian.Weyl.ESA.clm_essentiallySelfAdjoint`
- `Brockian.Weyl.ESA.id_essentiallySelfAdjoint`

Why generally useful: this gives a non-vacuous inhabitant of the deficiency-space
definition and a standard bridge from bounded self-adjoint `ContinuousLinearMap`s
to full-domain `LinearPMap`s.

Cleanup before PR:

- Depend on the upstreamed `IsSymmetric` and deficiency-space API.
- State the theorem with Mathlib naming around `ContinuousLinearMap.toPMap`.
- Decide whether `id_essentiallySelfAdjoint` is useful as an example or should be
  omitted from Mathlib.

### 10. Essential self-adjointness transfers across unitary equivalence

Local module: `Brockian.WeylFreeLaplacian2`

Local declarations:

- `Brockian.Weyl.FreeLaplacian2.dense_map_iff`
- `Brockian.Weyl.FreeLaplacian2.rangeSMulSub_image`
- `Brockian.Weyl.FreeLaplacian2.essentiallySelfAdjoint_transfer`
- Supporting bounded witness:
  `Brockian.Weyl.FreeLaplacian2.conjCLM_toPMap_essentiallySelfAdjoint_iff`

Why generally useful: unitary equivalence preserving dense shifted ranges and
essential self-adjointness is reusable in spectral theory, Fourier analysis, and
quantum-mechanical operator formalization.

Cleanup before PR:

- Generalize the statement away from the free-Laplacian file.
- Decide whether the hypothesis should be an equality of domains/actions or a
  bundled conjugation relation.
- Upstream after `rangeSMulSub` and `essentiallySelfAdjoint_iff`, because it
  depends naturally on those APIs.

### 10a. ESA is equivalent to self-adjoint graph closure

Local module: `Brockian.WeylUpstream`

Local declarations:

- `Brockian.Weyl.Upstream.deficiencySpace_eq_bot_of_closure_isSelfAdjoint`
- `Brockian.Weyl.Upstream.essentiallySelfAdjoint_iff_closure_isSelfAdjoint`

Why generally useful: this is the standard closure formulation of von
Neumann's criterion for a densely defined symmetric `LinearPMap`. It is the
bridge between the deficiency-space API and Mathlib's graph-closure API.

Cleanup before PR:

- Land only after the symmetric, deficiency-space, and closure APIs above.
- Move to the final `LinearPMap` namespace and reduce imports.
- Keep the dense-domain and symmetry hypotheses explicit.

### 10b. Maximal multiplication ESA from bounded unit resolvents

Local modules: `Brockian.WeylMaximalMultiplication`,
`Brockian.WeylMultiplicationUpstream`

Local declarations:

- `Brockian.Weyl.MaximalMultiplication.rangeSMulSub_maximalMul_eq_top`
- `Brockian.Weyl.MultiplicationUpstream.maximalMul_essentiallySelfAdjoint_of_unit_resolvents`

Why generally useful: explicit bounded pointwise inverses of the two unit
shifts give surjective shifted ranges and hence ESA of a densely defined maximal
multiplication operator. This is reusable for spectral multiplication models,
not specific to the free Laplacian.

Cleanup before PR:

- Separate construction of `maximalMul` from the ESA corollary.
- Generalize the measure-space assumptions only where Mathlib's `Lp` API allows.
- Replace project range names after the shifted-range API lands.

### 10c. Bounded Kato-Rellich for `LinearPMap`

Local module: `Brockian.WeylKatoRellich`

Local declarations:

- `Brockian.Weyl.KatoRellich.graphShear`
- `Brockian.Weyl.KatoRellich.graph_perturb_eq_shear_image`
- `Brockian.Weyl.KatoRellich.closure_perturb_eq_perturb_closure`
- `Brockian.Weyl.KatoRellich.isSelfAdjoint_perturb`
- `Brockian.Weyl.KatoRellich.essentiallySelfAdjoint_bounded_perturbation`

Why generally useful: this closes a genuine Mathlib infrastructure gap. The
proof uses a graph homeomorphism to commute closure with a bounded perturbation,
then computes the adjoint domain directly to preserve self-adjointness.

Cleanup before PR:

- Split graph closure compatibility from the Kato theorem if maintainers prefer
  smaller review units.
- Rename local `perturb` to the final `LinearPMap` bounded-addition API.
- Depend on the upstream closure/ESA equivalence instead of project namespaces.

### 11. Residue count saturation for large primes

Local module: `Brockian.SingularSeriesConvergence`

Local declarations:

- `Brockian.SingularSeries.Convergence.nu_p_eq_card_of_lt`
- Supporting definition: `Brockian.SingularSeries.nu_p`

Why generally useful: for a finite set of natural numbers, reducing modulo a
larger modulus is injective, so the number of distinct residues equals the set's
cardinality. This is a small but useful finite-set/modular-arithmetic lemma.

Cleanup before PR:

- Generalize from the local `nu_p` definition to a generic
  `Finset.card_image_of_injOn` corollary or a theorem about `Nat.mod`.
- Consider whether the modulus must be prime. The current theorem does not need
  primality.
- Place it in an existing `Nat.ModEq`/`Finset` area unless a singular-series file
  is created.

### 12. Singular-series local-factor tail and convergence infrastructure

Local modules: `Brockian.SingularSeries`, `Brockian.SingularSeriesConvergence`

Local declarations:

- `Brockian.SingularSeries.localFactor`
- `Brockian.SingularSeries.localFactorAt`
- `Brockian.SingularSeries.local_factor_pos`
- `Brockian.SingularSeries.singular_series_finite_pos`
- `Brockian.SingularSeries.Convergence.err_bound`
- `Brockian.SingularSeries.Convergence.localFactor_sub_one_bound`
- `Brockian.SingularSeries.Convergence.summable_localFactorAt_sub_one`
- `Brockian.SingularSeries.Convergence.singularSeriesFinite_tendsto_pos`
- `Brockian.SingularSeries.Convergence.singular_series_pos'`

Why generally useful: the finite Euler product and the summable
`abs (localFactorAt G p - 1)` pipeline are credible seeds for a Mathlib
singular-series/infinite-product API. The elementary Taylor bound `err_bound` is
also useful independently.

Cleanup before PR:

- Do not PR the current `singularSeries` definition as-is. Mathlib should likely
  use `Multipliable`/`tprod` rather than "choose a limit if it exists, else 0".
- Split the work: first `err_bound`, then finite residue/local-factor lemmas, then
  infinite-product convergence.
- Generalize admissibility assumptions and names away from Hardy-Littlewood tuple
  narrative where possible.
- Make sure no comments imply prime-distribution consequences.

### 13. `ZMod` finite admissibility counts and CRT product counts

Local modules: `Brockian.Admissibility`, `Brockian.AdmissibilityCRT`,
`Brockian.Sieve`

Local declarations:

- `Brockian.Admissibility.admissibleResidues`
- `Brockian.Admissibility.universal_admissibility_count`
- `Brockian.Admissibility.admissibility_count_three`
- `Brockian.Admissibility.admissibility_count_five`
- `Brockian.Admissibility.CRT.admissibleResidues_crt_card`
- `Brockian.Admissibility.CRT.admissibleResidues_crt_card_two_primes`
- Related: `Brockian.Sieve.TwinAdmissibleAt`
- Related: `Brockian.Sieve.twin_admissible_card`

Why generally useful: these are clean finite cardinality results over `ZMod`.
The CRT theorem is especially reusable: a filtered set pulled back along
`ZMod.chineseRemainder` has product cardinality.

Cleanup before PR:

- Separate the general finite-set facts from prime-pair language.
- Consider a generic theorem for complements of a two-point finset in a finite
  type, then specialize to `ZMod q`.
- For the CRT theorem, state a reusable lemma about an equivalence preserving a
  product predicate, then derive the `ZMod.chineseRemainder` corollary.
- Remove paper-correction prose from theorem docs.

### 14. C5/D5 finite automorphism, representation, and cyclic Fourier lemmas

Local modules: `Brockian.Automorphism`, `Brockian.AutomorphismFull`,
`Brockian.D5Representation`, `Brockian.D5Isotypic`,
`Brockian.D5FourierInversion`, `Brockian.D5LaplacianModes`

Local declarations:

- `Brockian.Automorphism.rot_map_adj`
- `Brockian.Automorphism.refl_map_adj`
- `Brockian.Automorphism.dihedral_action_faithful`
- `Brockian.Automorphism.Full.dihedralHom_surjective`
- `Brockian.Automorphism.Full.autEquivDihedral`
- `Brockian.Automorphism.Full.aut_card_eq_ten`
- `Brockian.D5Representation.coordSum_autPull`
- `Brockian.D5Representation.autPull_mem_constantLine`
- `Brockian.D5Representation.autPull_mem_zeroSumSubmodule`
- `Brockian.D5Representation.constantVector_mem_zeroSumSubmodule_iff`
- `Brockian.D5Isotypic.sum_omegaPow`
- `Brockian.D5Isotypic.character_orthogonality`
- `Brockian.D5Isotypic.isotypicProjector_eigenmode`
- `Brockian.D5FourierInversion.sum_isotypicProjectors`
- `Brockian.D5FourierInversion.fourier_inversion`
- `Brockian.D5FourierInversion.isotypicProjector_idempotent`
- `Brockian.D5FourierInversion.isotypicProjector_orthogonal`
- `Brockian.D5LaplacianModes.adjacency_eigenmode_cos`
- `Brockian.D5LaplacianModes.laplacian_eigenmode`

Why generally useful: the current code contains three upstreamable kernels:
`Aut(C5) ~= D5`, permutation-representation invariance of constants and zero-sum
functions, and discrete Fourier projector algebra over a finite cyclic group.

Cleanup before PR:

- Generalize from `5` to `n` where possible, with hypotheses such as `3 <= n`
  for cycle automorphisms.
- Do not upstream C5-only names as the primary API. Use `ZMod n`, `Fin n`, or
  finite cyclic-group notation.
- Replace proof-by-enumeration where a structural proof is reasonable.
- Split graph automorphisms, representation invariance, Fourier orthogonality,
  and Laplacian diagonalization into separate PRs.

### 15. Cycle-spectrum family and C5 multiplicity packaging

Local modules: `Brockian.Spectral`, `Brockian.CycleSpectrumFamily`,
`Brockian.C5SpectralMultiplicities`

Local declarations:

- `Brockian.Spectral.cycleSpectrum`
- `Brockian.CycleSpectrumFamily.mem_cycleSpectrum`
- `Brockian.CycleSpectrumFamily.two_mem_cycleSpectrum`
- `Brockian.CycleSpectrumFamily.cycleSpectrum_le_two`
- `Brockian.CycleSpectrumFamily.cycleSpectrum_ge_neg_two`
- `Brockian.CycleSpectrumFamily.lambda_max_cycle`
- `Brockian.CycleSpectrumFamily.cycleSpectrum_subset_Icc`
- `Brockian.CycleSpectrumFamily.laplacianCycleSpectrum`
- `Brockian.CycleSpectrumFamily.mem_laplacianCycleSpectrum`
- `Brockian.CycleSpectrumFamily.zero_mem_laplacianCycleSpectrum`
- `Brockian.CycleSpectrumFamily.algebraic_connectivity_mem`
- `Brockian.CycleSpectrumFamily.algebraic_connectivity_pos`
- `Brockian.CycleSpectrumFamily.laplacianCycleSpectrum_nonneg`
- `Brockian.CycleSpectrumFamily.laplacianCycleSpectrum_le_four`
- `Brockian.C5SpectralMultiplicities.c5SpectrumMultiset_eq`
- `Brockian.C5SpectralMultiplicities.multiplicity_two`
- `Brockian.C5SpectralMultiplicities.multiplicity_golden_sub_one`
- `Brockian.C5SpectralMultiplicities.multiplicity_neg_golden`
- `Brockian.C5SpectralMultiplicities.c5LaplacianMultiset_eq`
- `Brockian.C5SpectralMultiplicities.multiplicity_lap_zero`
- `Brockian.C5SpectralMultiplicities.multiplicity_lap_gap`
- `Brockian.C5SpectralMultiplicities.multiplicity_lap_large`

Why generally useful: Mathlib has graph theory and linear algebra, but this repo
has a concrete closed-form cycle-spectrum family and C5 multiplicity bookkeeping.
The reusable target is a graph/circulant spectral API for cycles, not a golden
ratio story.

Cleanup before PR:

- Connect `cycleSpectrum` to an actual adjacency matrix or `SimpleGraph` operator,
  not only a closed-form set definition.
- Generalize multiplicities from C5 to `C_n`: mode `k` and `n-k` have equal cosine
  value, with special cases for `k = 0` and, when `n` is even, `k = n/2`.
- Keep pentagon/golden facts as examples or tests after the general theorem lands.
- Avoid any claim that C5 spectra imply arithmetic distribution statements.

## Suggested PR Order

1. `LinearPMap.IsSymmetric` predicate plus real quadratic form and real eigenvalue
   lemmas.
2. Symmetric-operator inequality, `rangeSMulSub`, and the range/deficiency
   orthogonality identity.
3. Deficiency-space dense-range criterion, closed deficiency subspace, and bounded
   self-adjoint full-domain ESA.
4. `ZMod` finite counting and CRT product-cardinality lemmas, stripped of
   prime-pair language.
5. Finite cyclic Fourier/projector algebra and cycle-spectrum API, generalized
   from C5/D5 to `n`.
6. Singular-series convergence infrastructure after the local-factor definitions
   are redesigned around `tprod`/`Multipliable`.

## Lower Priority or Not Upstreamable As-Is

- `Brockian.Spectral.golden_unique_to_five` is mathematically valid local content,
  but it is too specialized for an early Mathlib PR unless embedded in a broader
  algebraic classification of cycle spectra.
- `Brockian.Weyl.Confining`, `Brockian.ConfiningSpectralShape`, and related
  Hilbert-Polya-shape files should not be upstreamed as project-specific bundles.
  Some bounded-operator lemmas inside them may already be covered by candidates
  above.
- Goldbach/equidistribution scaffolding is intentionally out of scope here.
