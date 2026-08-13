# BrockianCore Consolidation Report

Draft core library: `aristotle/core_consolidation/BrockianCore_draft.lean` (namespace `BrockianCore`).

Scope: the 10 duplicated definition names identified across `aristotle/best_proofs/Brockian_*.lean`
(254 island files). Every variant's exact text was extracted and compared; each object below records
the variants found, the canonical choice with rationale, genuine incompatibilities (same name,
different object), and the compatibility lemmas proposed as fleet targets.

Totals: **10 duplicated names → 21 canonical objects, 25 fleet-target compatibility lemmas.**

---

## 1. `Admissible` — 8 variants → 4 canonical objects

| File | Type | Formulation |
|---|---|---|
| `Brockian_AdmissibilityKTupleK4.lean` | `{k} (h : Fin k → ℤ)` | `∀ p prime, ∃ r : ZMod p, ∀ i, (h i : ZMod p) ≠ r` |
| `Brockian_SingularSeriesGaps12401250.lean` | `Finset ℤ` | `∃ r : ZMod p, ∀ a ∈ S, (a : ZMod p) ≠ r` |
| `Brockian_SingularSeriesGaps13501360.lean` | `Finset ℤ` | identical to 1240–1250 |
| `Brockian_SingularSeriesGaps9098.lean` | `Finset ℤ` | identical to 1240–1250 |
| `Brockian_SingularSeriesGaps7280.lean` | `Finset ℤ` | `(residues H p).card < p` (residue-count form) |
| `Brockian_SingularSeriesGaps14501460.lean` | `Finset ℤ` | `∃ r : ℕ, r < p ∧ ∀ x ∈ H, ¬ (p ∣ x − r)` (divisibility form) |
| `Brockian_SingularSeriesGaps16021610.lean` | `Finset ℕ` | `∃ r < p, ∀ x ∈ H, x % p ≠ r` |
| `Brockian_SophieGermain_SophieGermainInfinitude.lean` | `List (ℕ × ℕ)` | Dickson: `∀ q prime, ∃ n, ∀ (a,b) ∈ F, ¬ q ∣ a·n + b` |

**Canonical:** `Admissible (H : Finset ℤ)` in the `ZMod` form (the plurality form, 3 verbatim
occurrences; `ZMod` gives the cleanest Mathlib API for the singular-series work). Derived
canonical wrappers `AdmissibleTuple {k} (h : Fin k → ℤ) := Admissible (univ.image h)` and
`AdmissibleNat (H : Finset ℕ) := Admissible (H.image ↑·)` eliminate the type-level duplicates
without introducing independent definitions. Helper `residues` (from Gaps7280) is also canonical.

**Incompatibilities:** the Sophie Germain variant is a *genuinely different object* —
admissibility of a family of affine linear forms (Dickson's setting), not of a translate
pattern. Distinct canonical name **`AdmissibleForms`** (with `DicksonHypothesis` restated
against it). All other variants are provably equivalent reformulations.

**Fleet targets (4):**
1. `admissible_iff_residues_card_lt` — canonical ↔ residue-count form (Gaps7280).
2. `admissible_iff_forall_exists_not_dvd` — canonical ↔ divisibility form (Gaps14501460).
3. `admissibleTuple_iff` — wrapper ↔ pointwise `Fin` form (AdmissibilityKTupleK4).
4. `admissibleNat_iff` — wrapper ↔ `%`-form (Gaps16021610).

---

## 2. `freeLaplacian` — 5 variants → 3 canonical operators (+ canonical symbol)

| File | Type | Formulation |
|---|---|---|
| `Brockian_fourier_lineDerivOp_sq.lean` | `L2 V →ₗ.[ℂ] L2 V` | `conjPMap (fourierU V) (mulOp freeSymbol)` — **maximal** multiplier domain |
| `Brockian_FreeLaplacianPlancherel_..._via_plancherel.lean` | `𝓢(ℝ,ℂ) →L[ℂ] 𝓢(ℝ,ℂ)` | `-(derivCLM ∘L derivCLM)`, `V = ℝ` only |
| `Brockian_Weyl_FreeLaplacian2_continuous_symbol.lean` | `L2 d →ₗ.[ℂ] L2 d` | Schwartz-submodule domain, `-laplacianCLM`, `V = EuclSpace d` |
| `Brockian_Weyl_FreeLaplacian2_norm_sub_I_smul_sq.lean` | `𝓢(EuclSpace d,ℂ) →L[ℂ] 𝓢(...)` | `-∑ᵢ lineDerivOpCLM² ` |
| `Brockian_Weyl_FreeLaplacian2_..._of_fourier.lean` | `L2Space V →ₗ.[ℂ] L2Space V` | domain `range toL2`, `-laplacianCLM`, general `V` |

**Canonical (three genuinely different objects):**
- `negLaplacianCLM V : 𝓢(V,ℂ) →L[ℂ] 𝓢(V,ℂ) := -laplacianCLM ℂ V 𝓢(V,ℂ)` — Schwartz-side
  endomorphism, general finite-dimensional real inner product space `V` (most general setting
  any island uses; covers variants 2 and 4 through provable derivative-formula equalities).
- `freeLaplacian : L2 V →ₗ.[ℂ] L2 V` — unbounded operator with **Schwartz domain**
  (`schwartzSubmodule = range schwartzToL2`), covering variants 3 and 5 (which differ only in
  how they package the domain equivalence).
- `freeLaplacianMax : L2 V →ₗ.[ℂ] L2 V := conjPMap (fourierU V) (mulOp freeSymbol)` — variant 1.
  **Incompatibility:** its domain is the full maximal multiplier domain, strictly larger than the
  Schwartz space, so it is *not* the same operator as `freeLaplacian`; the islands'
  essential-self-adjointness theorems are exactly the statement `closure freeLaplacian = freeLaplacianMax`.
  Hence the distinct name.
- Canonical symbol `freeSymbol (ξ : V) := 4π²‖ξ‖²` (consolidates `freeSymbol` ×2 and `laplacianSymbol`).
- Supporting infra `mulDomain`/`mulFun`/`mulOp`, `conjPMap`, `fourierU`, `schwartzToL2`, `L2`
  copied verbatim (sorry-free proofs included) from `Brockian_fourier_lineDerivOp_sq.lean`,
  since `freeLaplacianMax` cannot be stated without them. The `L2`/`L2R`/`L2Space` abbreviation
  triplicates collapse to one `L2`.

**Fleet targets (7):** `negLaplacianCLM_apply_real` (1-D `deriv²` bridge),
`negLaplacianCLM_eq_sum_lineDeriv` (line-derivative-sum bridge),
`fourier_negLaplacianCLM` (symbol computation, currently proved 3× independently),
`freeLaplacian_le_freeLaplacianMax`, `isSelfAdjoint_freeLaplacianMax`,
`freeLaplacian_essentiallySelfAdjoint` (closure identity; statement shape to be fixed against
Mathlib's `LinearPMap` closure API), `freeLaplacian_domain_dense`.

---

## 3. `Equidistributed` — 4 variants → 3 canonical objects (1 merges into `EquidistributedMod1`)

| File | Type | Formulation |
|---|---|---|
| `Brockian_EquidistributionBVReduction_configCount_density_of_BV.lean` | `u : ℕ → ℝ` | continuous real tests, `∫_0^1`; **no mod-1 reduction** |
| `Brockian_Equidistribution_integral_fourier.lean` | `x : ℕ → AddCircle T` | continuous ℂ tests vs `haarAddCircle` |
| `Brockian_upperFn_nonneg.lean` | `a : ℝ` (rotation orbit) | continuous real tests on `Circ` along `pt a n` |
| `Brockian_sqrt_block.lean` | `x : ℕ → ℝ` | window-count form — is `EquidistributedMod1` under another name |

**Canonical:**
- `Equidistributed (x : ℕ → AddCircle T)` — the continuous-ℂ-test Weyl criterion (the intrinsic,
  most general circle form), with helper `avg` and companion `WeylSumsVanish`.
- `EquidistributedUnitInterval (u : ℕ → ℝ)` — **distinct object**: the BV-reduction island tests
  `f (u n)` directly with no `Int.fract`, so it is a statement about `[0,1]`-valued sequences,
  not sequences mod 1. Distinct name kept; agreement under `∀ n, u n ∈ [0,1)` is a fleet target.
- `EquidistributedOrbit (a : ℝ)` — canonical restatement of the orbit-specific variant through
  the canonical `Circ`/`pt` vocabulary; provably the specialization `Equidistributed (pt a)`
  (fleet target — needs ℝ-vs-ℂ tests and `volume = haarAddCircle` on `ℝ/ℤ`).
- The `sqrt_block` variant is *not* given a name: it is definitionally `EquidistributedMod1`.

## 4. `EquidistributedMod1` — 4 variants → 1 canonical object

Files: `Brockian_Equidistribution_integrable_of_continuousMap.lean` (via `countIn`),
`Brockian_eVariationOn_sub_le.lean`, `Brockian_EquidistributionBVReduction_geom_avg_tendsto.lean`,
`Brockian_volume_circ_univ.lean` — **all four literally identical** up to whether the filter-card
is inlined or named (`countIn`). No incompatibilities.

**Canonical:** `EquidistributedMod1 (x : ℕ → ℝ)` phrased through the canonical counting function
`windowCount` (see §5). Also absorbs `Equidistributed` of `Brockian_sqrt_block.lean`.

**Fleet targets for §3–4 (4):**
1. `equidistributedMod1_iff_equidistributed` — window form ↔ circle continuous-test form at `T = 1`
   (this *is* the theorem the BV-reduction islands prove; restated as the canonical bridge).
2. `equidistributedOrbit_iff` — orbit variant ↔ `Equidistributed (pt a)`.
3. `equidistributedUnitInterval_of_mod1` — agreement on `[0,1)`-valued sequences.
4. `weylSumsVanish_iff_weylCondition` — canonical `WeylSumsVanish` ↔ the exponential-sum
   `WeylCondition` of `Brockian_volume_circ_univ.lean`.

---

## 5. `configCount` — 6 variants → 1 canonical + 4 named specializations

| File | Type | Counts |
|---|---|---|
| `Brockian_EquidistributionBVReduction_configCount_density_of_BV.lean` | `(u : ℕ → ℝ) (S : Set ℝ) (N)` | `u n ∈ S`, `n < N` |
| `Brockian_EquidistributionBVReduction_configCount_over_main_tendsto.lean` | `(q a N : ℕ)` | `n ≡ a [MOD q]`, `n < N` |
| `Brockian_haar_eq_volume.lean` | `(α a b : ℝ) (N)` | `fract (n·α) ∈ [a,b)` |
| `Brockian_integrable_continuousMap.lean` | `(α a b : ℝ) (N)` | identical to `haar_eq_volume` |
| `Brockian_upperFn_nonneg.lean` | `(a c r : ℝ) (N)` | `dist (pt a n) c < r` on `Circ` |
| `Brockian_sqrt_block.lean` | `(w : ℝ → ℝ) (x : ℕ → ℝ) (N) : ℝ` | weighted sum `∑ w (fract (x n))` |

**Canonical:** `configCount (u : ℕ → ℝ) (S : Set ℝ) (N : ℕ) : ℕ` — the most general form; every
window-style count is an instance. Named specializations (distinct canonical names, since these
are five genuinely different counting functions sharing one name across islands):
- `windowCount (x a b N)` — fract-in-`Ico` count (also the engine of `EquidistributedMod1`);
- `orbitWindowCount (α a b N) := windowCount (fun n => n·α) a b N` — the two orbit islands;
- `apCount (q a N)` — congruence-class count (**different object**: counts indices, not values);
- `arcCount (a c r N)` — metric-ball count on the circle (**different object**: metric ball vs
  half-open window; the two disagree on endpoint/wrap-around behaviour);
- `weightedConfigCount (w x N) : ℝ` — real-valued weighted count (**different object**: ℝ-valued).

**Fleet targets (3):** `windowCount_eq_configCount` (decidability-transport identification),
`orbitWindowCount_eq` (bridge to the two orbit islands' inlined definition),
`weightedConfigCount_indicator` (indicator weight = plain window count, bridging `sqrt_block`).

---

## 6. `mainTerm` — 4 variants → 4 canonical objects (pure renames)

| File | Definition | Canonical name |
|---|---|---|
| `Brockian_countMultiples_eq_div.lean` | `N * Real.log N` | `divisorMainTerm` |
| `Brockian_EquidistributionBVReduction_configCount_over_main_tendsto.lean` | `N / q` | `apMainTerm` |
| `Brockian_integrable_continuousMap.lean` | `(b − a) * N` | `windowMainTerm` |
| `Brockian_upperFn_nonneg.lean` | `2r * N` | `arcMainTerm` |

**Incompatibility:** total — four unrelated quantities (divisor-sum asymptotics, AP density,
window density, arc density) shared one name. Consolidation is pure renaming; **no fleet
targets needed** (island theorems restate against the renamed constants definitionally).

---

## 7. `IsBetrothedPair` — 6 variants → 2 canonical objects

Files with the **strong form** (verbatim identical up to `σ 1` / `sigma 1` /
`ArithmeticFunction.sigma 1` notation): `BetrothedInfinitude`, `betrothed_5775_6128`,
`Dynamics_isBetrothedPair_iff_nontrivial_twoCycle`, `density_zero_reduction`,
`primePower_member_structure`:
`0 < m ∧ 0 < n ∧ m ≠ n ∧ σ₁ m = m + n + 1 ∧ σ₁ n = m + n + 1`.

**Incompatibility:** `Brockian_BetrothedNumbers_no_pair_of_mersenne_and_shifted_prime.lean`
deliberately **omits `m ≠ n`** (to strengthen its nonexistence theorem). This is *not* an
equivalent object: `IsBetrothedPairWeak m m` would make `m` quasiperfect (`σ₁ m = 2m + 1`),
whose existence is an open problem — so the weak form cannot be collapsed into the strong one.

**Canonical:** `IsBetrothedPair` (strong, phrased via canonical `sigmaOne`) and
`IsBetrothedPairWeak` (no distinctness). `betrothedNumbers` consolidates
`betrothedNumbers`/`betrothedSet`.

**Fleet targets (3):** `isBetrothedPair_iff_weak` (strong ↔ weak ∧ `m ≠ n`),
`IsBetrothedPair.symm`, `isBetrothedPair_iff_sigma` (notation bridge for the five σ-phrased islands).

---

## 8. `GoldbachWheelK2` — 4 variants → 2 canonical objects

| File | Formulation |
|---|---|
| `Brockian_GoldbachWheelK2_631.lean` | `∀ e : ZMod m, ∀ N, ∃ p q > N` primes, **coprime to m**, `(p+q : ZMod m) = e` |
| `Brockian_GoldbachWheelK2_727.lean` | same with `Nat.ModEq` target — equivalent to `_631` |
| `Brockian_GoldbachWheelK2_947.lean` | **no coprimality**: `∃ p q > N` primes, `(p:ZMod m)+(q:ZMod m) = r` |
| `Brockian_GoldbachWheelK2_1051.lean` | **finite verification**: `∀` even `n`, `10 ≤ n ≤ m` → `∃ p q` primes coprime to `6`, `p + q = n` |

**Incompatibilities:** `_1051` is a *genuinely different object* — a bounded, decidable Goldbach
check on the fixed wheel `m = 6`, where the parameter `m` is the verification *bound*, not the
modulus. Distinct canonical name **`GoldbachWheelK2UpTo`** (with `wheelK2Modulus = 6`). `_947`
drops the coprimality constraint, giving a weaker pointwise statement; kept as
**`GoldbachWheelK2Free`** with a one-directional bridge.

**Canonical:** `GoldbachWheelK2` = the strong coprime `ZMod` form (`_631`); `_727` is an
equivalent phrasing (fleet target); `GoldbachWheelK2Free` (`_947`); `GoldbachWheelK2UpTo` (`_1051`).

**Fleet targets (2):** `goldbachWheelK2_iff_modEq` (`ZMod` ↔ `Nat.ModEq` phrasing, absorbing
`_727`), `GoldbachWheelK2.free` (strong → coprimality-free, absorbing `_947`'s interface).

---

## 9. `traceNorm` — 3 variants → 1 canonical object

| File | Formulation |
|---|---|
| `Brockian_CosTraceNorm1279.lean` | `A : Matrix ι ι ℝ`, `traceNorm (hA : A.IsHermitian) := ∑ i, \|hA.eigenvalues i\|` |
| `Brockian_CosTraceNorm2003.lean` | same over ℂ |
| `Brockian_CosTraceNorm1597.lean` | `A : Matrix n n 𝕜` (`RCLike 𝕜`), `RCLike.re (trace (cfc \|·\| A))` — total function |

**Canonical:** the CFC form of `_1597`: it is a **total** function of the matrix (no `IsHermitian`
proof threaded through every signature), stated once over any `RCLike` field, so it subsumes
both the ℝ and ℂ eigenvalue-sum variants. Mild incompatibility: on non-Hermitian input it
returns the CFC junk value, whereas the other variants are simply not defined there — harmless,
since every island theorem carries a Hermitian hypothesis anyway.

**Fleet target (1):** `traceNorm_eq_sum_abs_eigenvalues` — for `hA : A.IsHermitian`,
`traceNorm A = ∑ i, |hA.eigenvalues i|` (instantiates at `𝕜 = ℝ` for `_1279` and `𝕜 = ℂ`
for `_2003`).

---

## 10. `sigmaOne` — 3 variants → 1 canonical object

| File | Definition |
|---|---|
| `Brockian_AmicableNumbers_AmicableInfinitude.lean` | `∑ d ∈ n.divisors, d` |
| `Brockian_BetrothedNumbers_Dynamics_thabit_balance_identity.lean` | `ArithmeticFunction.sigma 1 m` |
| `Brockian_BetrothedNumbers_no_pair_of_mersenne_and_shifted_prime.lean` | `∑ d ∈ n.divisors, d` |

All equal by `ArithmeticFunction.sigma_one_apply`. **Canonical:** the `ArithmeticFunction.sigma 1`
form, so the Mathlib multiplicativity/prime-power API applies directly. No incompatibilities.

**Fleet target (1):** `sigmaOne_eq_sum_divisors`.

---

## Fleet-target index (25)

Admissibility (4): `admissible_iff_residues_card_lt`, `admissible_iff_forall_exists_not_dvd`,
`admissibleTuple_iff`, `admissibleNat_iff`.
Goldbach wheel (2): `goldbachWheelK2_iff_modEq`, `GoldbachWheelK2.free`.
Equidistribution (4): `equidistributedMod1_iff_equidistributed`, `equidistributedOrbit_iff`,
`equidistributedUnitInterval_of_mod1`, `weylSumsVanish_iff_weylCondition`.
Counting (3): `windowCount_eq_configCount`, `orbitWindowCount_eq`, `weightedConfigCount_indicator`.
Betrothed (3): `isBetrothedPair_iff_weak`, `IsBetrothedPair.symm`, `isBetrothedPair_iff_sigma`.
Divisors (1): `sigmaOne_eq_sum_divisors`.
Trace norm (1): `traceNorm_eq_sum_abs_eigenvalues`.
Free Laplacian (7): `negLaplacianCLM_apply_real`, `negLaplacianCLM_eq_sum_lineDeriv`,
`fourier_negLaplacianCLM`, `freeLaplacian_le_freeLaplacianMax`, `isSelfAdjoint_freeLaplacianMax`,
`freeLaplacian_essentiallySelfAdjoint` (statement shape to be finalized against the
`LinearPMap` closure API), `freeLaplacian_domain_dense`.

## Notes / follow-ups (out of scope for this pass)

- The `Gaps*` islands also duplicate the singular-series local machinery
  (`localFactor` ×2, `singularSeriesFactor` ×2, `nu`, `gapSet` ×2 with different signatures) —
  a natural second consolidation wave on top of canonical `Admissible`/`residues`.
- Draft-file caveats: the file targets `import Mathlib` (Lean 4.30 toolchain per the repo);
  `laplacianCLM`, `LineDeriv.lineDerivOpCLM`, `Lp.fourierTransformₗᵢ`, and
  `SchwartzMap.injective_toLp` are used as Mathlib API exactly as the islands use them —
  the `freeLaplacian` section should be compile-checked first, as it is the only part with
  nontrivial term-mode definitions (the `mulOp`/`conjPMap` infrastructure is copied verbatim
  from the proven island `Brockian_fourier_lineDerivOp_sq.lean`).
- `wheelK2Modulus`, `Circ`, `pt`, `avg`, `residues`, `betrothedNumbers`, `windowCount` are
  supporting canonical names promoted from island-local helpers.
