/-
# BrockianCore — consolidated core library (DRAFT)

Canonical definitions consolidating the duplicated local objects of the 254
standalone Aristotle island files in `aristotle/best_proofs/`.

Duplication inventory consolidated here:
  * `Admissible`            — 8 island definitions → 4 canonical objects
  * `freeLaplacian`         — 5 island definitions → 3 canonical objects (+ symbol)
  * `Equidistributed`       — 4 island definitions → 3 canonical objects
  * `EquidistributedMod1`   — 4 island definitions → 1 canonical object
  * `configCount`           — 6 island definitions → 1 canonical + 4 named specializations
  * `IsBetrothedPair`       — 6 island definitions → 2 canonical objects (strong/weak)
  * `GoldbachWheelK2`       — 4 island definitions → 2 canonical objects
  * `mainTerm`              — 4 island definitions → 4 canonical objects (all distinct)
  * `traceNorm`             — 3 island definitions → 1 canonical object
  * `sigmaOne`              — 3 island definitions → 1 canonical object

Conventions:
  * This file contains DEFINITIONS ONLY — no `sorry`, no axioms.  Every
    compatibility lemma an island needs in order to be restated against the
    canonical definitions is recorded as a `-- FLEET TARGET:` comment, to be
    dispatched to the Aristotle fleet as a standalone proof obligation.
  * Where two island definitions sharing a name are genuinely different
    mathematical objects, both get distinct canonical names (documented in
    `CONSOLIDATION_REPORT.md`).
  * Verbatim-copied supporting infrastructure (the `mulOp` / `conjPMap`
    unbounded-operator toolkit) is taken from
    `Brockian_fourier_lineDerivOp_sq.lean` including its (sorry-free) proofs,
    since the canonical `freeLaplacianMax` cannot be *stated* without it.

Companion document: `aristotle/core_consolidation/CONSOLIDATION_REPORT.md`.
-/
import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace BrockianCore

/-! ## 1. Divisor sums — `sigmaOne`

Consolidates: `Brockian_AmicableNumbers_AmicableInfinitude.lean`,
`Brockian_BetrothedNumbers_Dynamics_thabit_balance_identity.lean`,
`Brockian_BetrothedNumbers_no_pair_of_mersenne_and_shifted_prime.lean`.

Two islands define `sigmaOne n := ∑ d ∈ n.divisors, d`; one defines it as
`ArithmeticFunction.sigma 1 n`.  These are equal (`ArithmeticFunction.sigma_one_apply`).
Canonical choice: the `ArithmeticFunction` form, so every Mathlib `sigma` lemma
applies definitionally through `ArithmeticFunction.sigma`. -/

/-- The sum-of-divisors function `σ₁ n = ∑_{d ∣ n} d`. -/
def sigmaOne (n : ℕ) : ℕ := ArithmeticFunction.sigma 1 n

-- FLEET TARGET: theorem sigmaOne_eq_sum_divisors (n : ℕ) :
--   sigmaOne n = ∑ d ∈ n.divisors, d
--   (bridges the two `∑ d ∈ n.divisors, d` islands; proof: `ArithmeticFunction.sigma_one_apply`).

/-! ## 2. Betrothed (quasi-amicable) pairs — `IsBetrothedPair`

Consolidates: `Brockian_BetrothedNumbers_BetrothedInfinitude.lean`,
`Brockian_BetrothedNumbers_betrothed_5775_6128.lean`,
`Brockian_BetrothedNumbers_Dynamics_isBetrothedPair_iff_nontrivial_twoCycle.lean`,
`Brockian_BetrothedNumbers_density_zero_reduction.lean`,
`Brockian_BetrothedNumbers_primePower_member_structure.lean`,
`Brockian_BetrothedNumbers_no_pair_of_mersenne_and_shifted_prime.lean`.

Five islands agree verbatim up to `σ`-notation:
`0 < m ∧ 0 < n ∧ m ≠ n ∧ σ₁ m = m + n + 1 ∧ σ₁ n = m + n + 1`.
The sixth (`no_pair_of_mersenne_and_shifted_prime`) deliberately DROPS the
distinctness clause `m ≠ n` (to make its nonexistence theorem stronger).  The
two are NOT interchangeable: `IsBetrothedPairWeak m m` would require `σ₁ m = 2m + 1`,
i.e. `m` quasiperfect — an open problem — so the weak form is kept as a genuinely
distinct canonical object. -/

/-- `m` and `n` form a betrothed (quasi-amicable) pair: distinct positive integers,
each equal to the sum of the nontrivial proper divisors of the other; equivalently
`σ₁ m = σ₁ n = m + n + 1`. -/
def IsBetrothedPair (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ sigmaOne m = m + n + 1 ∧ sigmaOne n = m + n + 1

/-- The betrothed condition without the distinctness clause (the form used by the
Mersenne/shifted-prime nonexistence island, where dropping `m ≠ n` strengthens the
nonexistence result).  `IsBetrothedPairWeak m m ↔ m` is quasiperfect, an open problem,
so this is genuinely weaker than `IsBetrothedPair`. -/
def IsBetrothedPairWeak (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ sigmaOne m = m + n + 1 ∧ sigmaOne n = m + n + 1

/-- The set of numbers belonging to some betrothed pair
(consolidates `betrothedNumbers` / `betrothedSet`). -/
def betrothedNumbers : Set ℕ := {m | ∃ n, IsBetrothedPair m n}

-- FLEET TARGET: theorem isBetrothedPair_iff_weak (m n : ℕ) :
--   IsBetrothedPair m n ↔ IsBetrothedPairWeak m n ∧ m ≠ n
--   (trivial unfold; lets the weak-island theorem be specialized to the strong form).
-- FLEET TARGET: theorem IsBetrothedPair.symm {m n : ℕ} :
--   IsBetrothedPair m n → IsBetrothedPair n m
--   (re-proves the symmetry lemma of `BetrothedInfinitude` against the canonical form).
-- FLEET TARGET: theorem isBetrothedPair_iff_sigma (m n : ℕ) :
--   IsBetrothedPair m n ↔
--     0 < m ∧ 0 < n ∧ m ≠ n ∧
--       ArithmeticFunction.sigma 1 m = m + n + 1 ∧ ArithmeticFunction.sigma 1 n = m + n + 1
--   (definitional bridge for the five σ-phrased islands; proof: `Iff.rfl` after unfolding).

/-! ## 3. Admissibility of prime patterns — `Admissible`

Consolidates: `Brockian_AdmissibilityKTupleK4.lean` (Fin-tuple form),
`Brockian_SingularSeriesGaps12401250.lean`, `Brockian_SingularSeriesGaps13501360.lean`,
`Brockian_SingularSeriesGaps9098.lean` (Finset ℤ, ZMod form),
`Brockian_SingularSeriesGaps7280.lean` (Finset ℤ, residue-count form),
`Brockian_SingularSeriesGaps14501460.lean` (Finset ℤ, divisibility form),
`Brockian_SingularSeriesGaps16021610.lean` (Finset ℕ, `%`-form),
`Brockian_SophieGermain_SophieGermainInfinitude.lean` (Dickson linear-forms form —
a genuinely different object, kept as `AdmissibleForms`).

Canonical choice: the `Finset ℤ` / `ZMod` form (the plurality form, and the one all
`Finset`-flavoured variants are provably equivalent to).  The Fin-tuple and
Finset-ℕ variants are DEFINED THROUGH the canonical predicate so no independent
duplicate remains. -/

/-- The set of residue classes mod `p` occupied by a pattern `H ⊆ ℤ`
(from `Brockian_SingularSeriesGaps7280.lean`). -/
def residues (H : Finset ℤ) (p : ℕ) : Finset (ZMod p) :=
  H.image (fun h : ℤ => (Int.cast h : ZMod p))

/-- A finite pattern `H ⊆ ℤ` is *admissible* (in the sense of the Hardy–Littlewood
prime `k`-tuple conjecture) if for every prime `p` it misses at least one residue
class modulo `p`; equivalently, no local factor of the singular series vanishes. -/
def Admissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r

/-- Admissibility of an indexed `k`-tuple `h : Fin k → ℤ`
(canonicalizes the pointwise form of `Brockian_AdmissibilityKTupleK4.lean`
through the `Finset` predicate). -/
def AdmissibleTuple {k : ℕ} (h : Fin k → ℤ) : Prop :=
  Admissible (Finset.univ.image h)

/-- Admissibility of a pattern of naturals
(canonicalizes `Brockian_SingularSeriesGaps16021610.lean` through the `Finset ℤ`
predicate). -/
def AdmissibleNat (H : Finset ℕ) : Prop :=
  Admissible (H.image (fun n : ℕ => (n : ℤ)))

/-- Dickson admissibility of a finite family of linear forms `n ↦ a·n + b`
(from `Brockian_SophieGermain_SophieGermainInfinitude.lean`): no prime divides
all products of values.  A genuinely different object from pattern admissibility
(it quantifies over values of affine forms, not translates of a fixed pattern),
hence a distinct canonical name. -/
def AdmissibleForms (F : List (ℕ × ℕ)) : Prop :=
  ∀ q : ℕ, q.Prime → ∃ n : ℕ, ∀ ab ∈ F, ¬ (q ∣ ab.1 * n + ab.2)

/-- Dickson's conjecture for linear forms with natural coefficients, phrased against
the canonical `AdmissibleForms` (hypothesis-only; used by the Sophie Germain island). -/
def DicksonHypothesis : Prop :=
  ∀ F : List (ℕ × ℕ), (∀ ab ∈ F, 1 ≤ ab.1) → AdmissibleForms F →
    ∀ N : ℕ, ∃ n : ℕ, N < n ∧ ∀ ab ∈ F, (ab.1 * n + ab.2).Prime

-- FLEET TARGET: theorem admissible_iff_residues_card_lt (H : Finset ℤ) :
--   Admissible H ↔ ∀ p : ℕ, p.Prime → (residues H p).card < p
--   (bridges `Brockian_SingularSeriesGaps7280.lean`; uses `Finset.card_lt_iff_ne_univ`
--    / `ZMod.card p` for the prime `p`).
-- FLEET TARGET: theorem admissible_iff_forall_exists_not_dvd (H : Finset ℤ) :
--   Admissible H ↔
--     ∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ x ∈ H, ¬ ((p : ℤ) ∣ (x - (r : ℤ)))
--   (bridges `Brockian_SingularSeriesGaps14501460.lean`; via `ZMod.natCast_self_eq_zero`,
--    `ZMod.intCast_zmod_eq_zero_iff_dvd` and surjectivity of `Nat.cast : Fin p → ZMod p`).
-- FLEET TARGET: theorem admissibleTuple_iff {k : ℕ} (h : Fin k → ℤ) :
--   AdmissibleTuple h ↔ ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ i, (h i : ZMod p) ≠ r
--   (bridges `Brockian_AdmissibilityKTupleK4.lean`; proof: `Finset.mem_image` unfold).
-- FLEET TARGET: theorem admissibleNat_iff (H : Finset ℕ) :
--   AdmissibleNat H ↔ ∀ p : ℕ, p.Prime → ∃ r < p, ∀ x ∈ H, x % p ≠ r
--   (bridges `Brockian_SingularSeriesGaps16021610.lean`; via `ZMod.natCast_eq_iff` /
--    `Nat.mod_lt` and the `ZMod.val` round trip).

/-! ## 4. Goldbach wheel conditions — `GoldbachWheelK2`

Consolidates: `Brockian_GoldbachWheelK2_631.lean`, `Brockian_GoldbachWheelK2_727.lean`,
`Brockian_GoldbachWheelK2_947.lean`, `Brockian_GoldbachWheelK2_1051.lean`.

Three islands state an asymptotic residue-wheel condition; `_631` (coprime, `ZMod`
target) and `_727` (coprime, `Nat.ModEq` target) are equivalent, and `_947` drops the
coprimality constraints (strictly weaker as a pointwise statement — every-residue
coverage by arbitrary large primes).  `_1051` is a DIFFERENT object entirely: a
finite Goldbach verification up to a bound on the fixed wheel `m = 6`.  Canonical
choices: the strong coprime `ZMod` form (`GoldbachWheelK2`), the coprimality-free
form (`GoldbachWheelK2Free`), and the bounded verification (`GoldbachWheelK2UpTo`). -/

/-- The order-2 Goldbach wheel condition at modulus `m`: every residue class mod `m`
is the class of a sum of two arbitrarily large primes, each coprime to `m`
(canonical strong form, from `Brockian_GoldbachWheelK2_631.lean`). -/
def GoldbachWheelK2 (m : ℕ) : Prop :=
  ∀ (e : ZMod m) (N : ℕ), ∃ p q : ℕ,
    N < p ∧ N < q ∧ Nat.Prime p ∧ Nat.Prime q ∧
      Nat.Coprime p m ∧ Nat.Coprime q m ∧ ((p + q : ℕ) : ZMod m) = e

/-- The coprimality-free wheel condition (from `Brockian_GoldbachWheelK2_947.lean`):
every residue class mod `m` is a sum of two arbitrarily large primes, with no wheel
constraint on the primes.  Implied by `GoldbachWheelK2 m` but not conversely in
general, hence a distinct canonical name. -/
def GoldbachWheelK2Free (m : ℕ) : Prop :=
  ∀ (N : ℕ) (r : ZMod m), ∃ p q : ℕ,
    N < p ∧ N < q ∧ Nat.Prime p ∧ Nat.Prime q ∧ (p : ZMod m) + (q : ZMod m) = r

/-- The fixed `K = 2` wheel modulus used by the finite verification islands. -/
def wheelK2Modulus : ℕ := 6

/-- Finite Goldbach verification on the `K = 2` wheel (from
`Brockian_GoldbachWheelK2_1051.lean`): every even `n` with `10 ≤ n ≤ m` is a sum of
two primes both coprime to `6`.  A bounded, checkable statement — a genuinely
different object from the asymptotic wheel conditions above, hence its own name. -/
def GoldbachWheelK2UpTo (m : ℕ) : Prop :=
  ∀ n : ℕ, 10 ≤ n → n ≤ m → 2 ∣ n →
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧
      Nat.Coprime p wheelK2Modulus ∧ Nat.Coprime q wheelK2Modulus ∧ p + q = n

-- FLEET TARGET: theorem goldbachWheelK2_iff_modEq (m : ℕ) :
--   GoldbachWheelK2 m ↔
--     ∀ n N : ℕ, ∃ p q : ℕ, N < p ∧ N < q ∧ Nat.Prime p ∧ Nat.Prime q ∧
--       Nat.Coprime p m ∧ Nat.Coprime q m ∧ (p + q) ≡ n [MOD m]
--   (bridges `Brockian_GoldbachWheelK2_727.lean`; via `ZMod.natCast_eq_natCast_iff`
--    and surjectivity of `Nat.cast : ℕ → ZMod m`).
-- FLEET TARGET: theorem GoldbachWheelK2.free {m : ℕ} :
--   GoldbachWheelK2 m → GoldbachWheelK2Free m
--   (bridges `Brockian_GoldbachWheelK2_947.lean`; drop the coprimality conjuncts and
--    rewrite `((p + q : ℕ) : ZMod m)` with `Nat.cast_add`).

/-! ## 5. Equidistribution — `Equidistributed` / `EquidistributedMod1`

Consolidates the 4 `EquidistributedMod1` islands
(`Brockian_Equidistribution_integrable_of_continuousMap.lean`,
`Brockian_eVariationOn_sub_le.lean`,
`Brockian_EquidistributionBVReduction_geom_avg_tendsto.lean`,
`Brockian_volume_circ_univ.lean` — all literally identical up to the name of the
counting function) and the 4 `Equidistributed` islands, of which:
  * `Brockian_sqrt_block.lean` is EquidistributedMod1 under another name;
  * `Brockian_Equidistribution_integral_fourier.lean` is the continuous-test
    (Weyl) criterion on `AddCircle T` — canonical `Equidistributed`;
  * `Brockian_EquidistributionBVReduction_configCount_density_of_BV.lean` is the
    continuous-test criterion for a sequence taking values in `[0,1]` — kept as
    `EquidistributedUnitInterval` (it does NOT reduce mod 1, so it is a distinct
    object from both of the above);
  * `Brockian_upperFn_nonneg.lean` is the orbit-specialised ℝ-valued-test criterion
    on `ℝ/ℤ` — restated below as `EquidistributedOrbit` through canonical
    circle vocabulary. -/

/-- The circle `ℝ/ℤ` (from `Brockian_upperFn_nonneg.lean`). -/
abbrev Circ := AddCircle (1 : ℝ)

/-- The rotation orbit point `n • a` on `ℝ/ℤ`. -/
def pt (a : ℝ) (n : ℕ) : Circ := (((n : ℝ) * a : ℝ) : Circ)

/-- The number of indices `n < N` with `Int.fract (x n) ∈ [a, b)` — the canonical
window-counting function (named `countIn` / `windowCount` / inlined in the islands). -/
def windowCount (x : ℕ → ℝ) (a b : ℝ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico a b).card

/-- A sequence of reals is *equidistributed modulo one* when, for every subinterval
`[a, b) ⊆ [0, 1]`, the proportion of the first `N` fractional parts lying in `[a, b)`
tends to the length `b - a`.  (Canonical form of all four `EquidistributedMod1`
islands and of the `Equidistributed` of `Brockian_sqrt_block.lean`.) -/
def EquidistributedMod1 (x : ℕ → ℝ) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
    Filter.Tendsto (fun N : ℕ => (windowCount x a b N : ℝ) / N)
      Filter.atTop (nhds (b - a))

section circle

variable {T : ℝ} [hT : Fact (0 < T)]

/-- The empirical average of `f` along the first `N` terms of `x`
(from `Brockian_Equidistribution_integral_fourier.lean`). -/
def avg (x : ℕ → AddCircle T) (f : C(AddCircle T, ℂ)) (N : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, f (x n)

/-- A sequence in `AddCircle T` is *equidistributed* if its empirical averages converge
to the integral against the normalised Haar probability measure, for every continuous
complex test function.  (Canonical form of
`Brockian_Equidistribution_integral_fourier.lean`.) -/
def Equidistributed (x : ℕ → AddCircle T) : Prop :=
  ∀ f : C(AddCircle T, ℂ),
    Filter.Tendsto (avg x f) Filter.atTop (nhds (∫ t, f t ∂AddCircle.haarAddCircle))

/-- The Weyl-sum hypothesis: all nontrivial exponential sums have vanishing averages
(from `Brockian_Equidistribution_integral_fourier.lean`; the `WeylCondition` of
`Brockian_volume_circ_univ.lean` is its `x : ℕ → ℝ` avatar — see FLEET TARGET). -/
def WeylSumsVanish (x : ℕ → AddCircle T) : Prop :=
  ∀ k : ℤ, k ≠ 0 → Filter.Tendsto (avg x (fourier k)) Filter.atTop (nhds 0)

end circle

/-- Equidistribution of a sequence taking values in the unit interval, tested against
continuous real functions on ℝ with the integral over `[0,1]` (canonical form of
`Brockian_EquidistributionBVReduction_configCount_density_of_BV.lean`).  NOTE: this
does not reduce `u` modulo 1, so it is a genuinely different object from
`EquidistributedMod1`; the two agree when `∀ n, u n ∈ [0,1)` (fleet target below). -/
def EquidistributedUnitInterval (u : ℕ → ℝ) : Prop :=
  ∀ f : ℝ → ℝ, Continuous f →
    Filter.Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f (u n)) / N)
      Filter.atTop (nhds (∫ x in (0 : ℝ)..1, f x))

/-- Equidistribution of the rotation orbit `n ↦ n • a` on `ℝ/ℤ`, tested against
continuous real functions (canonical restatement of the orbit-specific
`Equidistributed a` of `Brockian_upperFn_nonneg.lean`). -/
def EquidistributedOrbit (a : ℝ) : Prop :=
  ∀ f : C(Circ, ℝ),
    Filter.Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, f (pt a n))
      Filter.atTop (nhds (∫ x : Circ, f x))

-- FLEET TARGET: theorem equidistributedMod1_iff_equidistributed (x : ℕ → ℝ) :
--   EquidistributedMod1 x ↔ Equidistributed (T := 1) (fun n => ((x n : ℝ) : AddCircle (1:ℝ)))
--   (the Weyl equivalence between the window form and the continuous-test form on ℝ/ℤ;
--    this is exactly the content the BV-reduction islands prove — restate their main
--    theorems through this bridge).
-- FLEET TARGET: theorem equidistributedOrbit_iff (a : ℝ) :
--   EquidistributedOrbit a ↔ Equidistributed (T := 1) (pt a)
--   (ℝ-valued vs ℂ-valued test functions, plus `volume = haarAddCircle` on `ℝ/ℤ`
--    (`AddCircle.volume_eq_smul_haarAddCircle` at `T = 1`); bridges
--    `Brockian_upperFn_nonneg.lean` to the canonical circle predicate).
-- FLEET TARGET: theorem equidistributedUnitInterval_of_mod1 (u : ℕ → ℝ)
--     (hu : ∀ n, u n ∈ Set.Ico (0 : ℝ) 1) :
--   EquidistributedMod1 u ↔ EquidistributedUnitInterval u
--   (on `[0,1)`-valued sequences `Int.fract (u n) = u n`; bridges the BV-density island).
-- FLEET TARGET: theorem weylSumsVanish_iff_weylCondition (x : ℕ → ℝ) :
--   WeylSumsVanish (T := 1) (fun n => ((x n : ℝ) : AddCircle (1:ℝ))) ↔
--     ∀ k : ℤ, k ≠ 0 → Filter.Tendsto
--       (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, Complex.exp (2 * π * Complex.I * k * x n))
--       Filter.atTop (nhds 0)
--   (bridges the `WeylCondition` of `Brockian_volume_circ_univ.lean`; via `fourier_coe_apply`).

/-! ## 6. Configuration counts — `configCount` and named specializations

Six islands use the name `configCount` for FIVE genuinely different counting
functions.  Canonical choice: the most general one — counting terms of an arbitrary
real sequence in an arbitrary target set (from
`Brockian_EquidistributionBVReduction_configCount_density_of_BV.lean`).  The
orbit-window variants are recovered definitionally via `windowCount`; the
arithmetic-progression, circle-arc and weighted variants are distinct objects with
their own canonical names. -/

open Classical in
/-- `configCount u S N` is the number of indices `n < N` for which `u n` lies in `S`
(canonical general form). -/
def configCount (u : ℕ → ℝ) (S : Set ℝ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun n => u n ∈ S)).card

/-- Orbit window count: the number of `n < N` with `Int.fract (n·α) ∈ [a, b)`
(the `configCount` of `Brockian_haar_eq_volume.lean` and
`Brockian_integrable_continuousMap.lean`, canonicalized through `windowCount`). -/
def orbitWindowCount (α a b : ℝ) (N : ℕ) : ℕ :=
  windowCount (fun n => (n : ℝ) * α) a b N

/-- Arithmetic-progression count: the number of `n < N` with `n ≡ a [MOD q]`
(the `configCount` of
`Brockian_EquidistributionBVReduction_configCount_over_main_tendsto.lean` —
a different object: it counts congruence configurations, not window hits). -/
def apCount (q a N : ℕ) : ℕ :=
  {n ∈ Finset.range N | n ≡ a [MOD q]}.card

open Classical in
/-- Circle-arc count: the number of `n < N` for which the orbit point `n • a` lies
within distance `r` of `c` on `ℝ/ℤ` (the `configCount` of
`Brockian_upperFn_nonneg.lean` — a metric-ball count on the circle, not a
half-open window count, hence a distinct object). -/
def arcCount (a c r : ℝ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun n => dist (pt a n) ((c : ℝ) : Circ) < r)).card

/-- Weighted configuration count: `∑_{n < N} w (fract (x n))` (the real-valued
`configCount` of `Brockian_sqrt_block.lean`; for `w` an indicator this is
`windowCount`, but as an ℝ-valued weighted sum it is a distinct object). -/
def weightedConfigCount (w : ℝ → ℝ) (x : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, w (Int.fract (x n))

-- FLEET TARGET: theorem windowCount_eq_configCount (x : ℕ → ℝ) (a b : ℝ) (N : ℕ) :
--   windowCount x a b N = configCount (fun n => Int.fract (x n)) (Set.Ico a b) N
--   (definitional up to `Classical` decidability transport; `Finset.filter_congr_decidable`).
-- FLEET TARGET: theorem orbitWindowCount_eq (α a b : ℝ) (N : ℕ) :
--   orbitWindowCount α a b N
--     = ((Finset.range N).filter fun n : ℕ => Int.fract ((n : ℝ) * α) ∈ Set.Ico a b).card
--   (bridges the inlined counts of `Brockian_haar_eq_volume.lean` and
--    `Brockian_integrable_continuousMap.lean`; proof: `rfl`/decidability transport).
-- FLEET TARGET: theorem weightedConfigCount_indicator (a b : ℝ) (x : ℕ → ℝ) (N : ℕ) :
--   weightedConfigCount ((Set.Ico a b).indicator fun _ => (1 : ℝ)) x N
--     = (windowCount x a b N : ℝ)
--   (bridges `Brockian_sqrt_block.lean`'s weighted count to the plain window count;
--    `Finset.card_filter` + `Finset.sum_congr`).

/-! ## 7. Main terms — four distinct objects

Four islands each call their expected main term `mainTerm`; the four quantities are
UNRELATED (divisor-sum asymptotics, AP density, window density, arc density), so
each gets its own canonical name.  Pure renames — no compatibility lemmas needed. -/

/-- The predicted main term `N log N` of the divisor summatory function
`∑_{n ≤ N} d(n)` (the `mainTerm` of `Brockian_countMultiples_eq_div.lean`). -/
def divisorMainTerm (N : ℕ) : ℝ := N * Real.log N

/-- The expected main term `N / q` for `apCount q a N` (the `mainTerm` of
`Brockian_EquidistributionBVReduction_configCount_over_main_tendsto.lean`). -/
def apMainTerm (q N : ℕ) : ℝ := (N : ℝ) / (q : ℝ)

/-- The expected main term `(b - a) · N` for a window count (the `mainTerm` of
`Brockian_integrable_continuousMap.lean`). -/
def windowMainTerm (a b : ℝ) (N : ℕ) : ℝ := (b - a) * N

/-- The expected main term `2r · N` for the arc count of radius `r` (the `mainTerm`
of `Brockian_upperFn_nonneg.lean`). -/
def arcMainTerm (r : ℝ) (N : ℕ) : ℝ := 2 * r * N

/-! ## 8. Trace norm — `traceNorm`

Consolidates: `Brockian_CosTraceNorm1279.lean` (real symmetric, eigenvalue sum),
`Brockian_CosTraceNorm2003.lean` (complex Hermitian, eigenvalue sum),
`Brockian_CosTraceNorm1597.lean` (RCLike, continuous functional calculus).

Canonical choice: the CFC form of `_1597` — it is a TOTAL function of the matrix
(no `IsHermitian` argument threaded through every statement), it is stated over any
`RCLike` field so it simultaneously generalizes the ℝ and ℂ islands, and it agrees
with the eigenvalue sum on Hermitian matrices (fleet target below). -/

section traceNorm

variable {n : Type*} [Fintype n] [DecidableEq n] {𝕜 : Type*} [RCLike 𝕜]

/-- The **trace norm** (nuclear norm, Schatten 1-norm) of a matrix over an `RCLike`
field: the trace of `|A|` via the continuous functional calculus.  On Hermitian
matrices this is the sum of the absolute values of the eigenvalues; on
non-Hermitian input it takes the CFC junk value. -/
def traceNorm (A : Matrix n n 𝕜) : ℝ :=
  RCLike.re (Matrix.trace (cfc (fun x : ℝ => |x|) A))

-- FLEET TARGET: theorem traceNorm_eq_sum_abs_eigenvalues {A : Matrix n n 𝕜}
--     (hA : A.IsHermitian) : traceNorm A = ∑ i, |hA.eigenvalues i|
--   (bridges `Brockian_CosTraceNorm1279.lean` (𝕜 = ℝ) and
--    `Brockian_CosTraceNorm2003.lean` (𝕜 = ℂ) to the canonical CFC form; via the
--    islands' own `trace_cfc_eq` argument: `Matrix.IsHermitian.cfc` diagonalisation
--    plus `Matrix.trace` of the diagonal).

end traceNorm

/-! ## 9. The free Laplacian — `freeLaplacian`

Consolidates: `Brockian_fourier_lineDerivOp_sq.lean` (maximal Fourier-side domain),
`Brockian_FreeLaplacianPlancherel_freeLaplacian_essentiallySelfAdjoint_via_plancherel.lean`
(Schwartz endomorphism, `V = ℝ`, iterated `derivCLM`),
`Brockian_Weyl_FreeLaplacian2_continuous_symbol.lean` (unbounded, Schwartz domain,
`V = EuclSpace d`),
`Brockian_Weyl_FreeLaplacian2_norm_sub_I_smul_sq.lean` (Schwartz endomorphism,
`-∑ lineDeriv²`),
`Brockian_Weyl_FreeLaplacian2_freeLaplacian_essentiallySelfAdjoint_of_fourier.lean`
(unbounded, Schwartz domain, general `V`).

Three genuinely different canonical objects:
  * `negLaplacianCLM V` — the Schwartz-space endomorphism `-Δ` (variants 2 and 4
    are its `V = ℝ` and `V = EuclSpace d` incarnations, via different but provably
    equal derivative formulas);
  * `freeLaplacian V`   — the unbounded operator on `L²(V)` with Schwartz domain
    (variants 3 and 5);
  * `freeLaplacianMax V` — the maximal-domain operator `𝓕⁻¹ (4π²‖ξ‖²·) 𝓕`
    (variant 1).  Its domain is the full multiplier domain, strictly larger than
    the Schwartz space, so it is NOT the same operator as `freeLaplacian` — the
    essential-self-adjointness theorems say precisely that `freeLaplacianMax` is
    the closure of `freeLaplacian`.
All are stated over a general finite-dimensional real inner product space `V`, the
most general setting any island uses. -/

section freeLaplacian

open MeasureTheory SchwartzMap Filter
open scoped ENNReal ComplexInnerProductSpace FourierTransform SchwartzMap Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The complex `L²` space of a finite-dimensional real inner product space, with
respect to the Lebesgue (volume) measure (consolidates the `L2` / `L2R` / `L2Space`
abbreviations of the five islands). -/
abbrev L2 (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] := Lp (α := V) ℂ 2 (volume : Measure V)

/-- The Fourier symbol `4π²‖ξ‖²` of the free Laplacian `-Δ` (consolidates
`freeSymbol` of `Brockian_fourier_lineDerivOp_sq.lean` /
`Brockian_Weyl_FreeLaplacian2_norm_sub_I_smul_sq.lean` and `laplacianSymbol` of the
Plancherel island). -/
def freeSymbol (ξ : V) : ℝ := 4 * π ^ 2 * ‖ξ‖ ^ 2

/-- The free Laplacian `-Δ` acting on Schwartz functions (canonical Schwartz-side
form; the islands' `freeLaplacian : 𝓢 →L 𝓢`, `negLaplacianCLM` and
`freeLaplacianSchwartz` all reduce to this). -/
def negLaplacianCLM (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ) :=
  -laplacianCLM ℂ V 𝓢(V, ℂ)

/-- The inclusion of the Schwartz space into `L²(V)` as a linear map (consolidates
`toL2` / `schwartzToL2`). -/
def schwartzToL2 : 𝓢(V, ℂ) →ₗ[ℂ] L2 V :=
  (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure V)).toLinearMap

/-- The Schwartz space viewed as a submodule of `L²(V)`: the canonical domain of the
free Laplacian. -/
def schwartzSubmodule : Submodule ℂ (L2 V) :=
  LinearMap.range (schwartzToL2 (V := V))

/-- The free Laplacian `-Δ` as an unbounded operator on `L²(V)` with the Schwartz
space as its domain (canonical form of the unbounded-with-Schwartz-domain variants
of `Brockian_Weyl_FreeLaplacian2_continuous_symbol.lean` and
`Brockian_Weyl_FreeLaplacian2_freeLaplacian_essentiallySelfAdjoint_of_fourier.lean`). -/
def freeLaplacian : L2 V →ₗ.[ℂ] L2 V where
  domain := schwartzSubmodule (V := V)
  toFun :=
    ((schwartzToL2 (V := V)).comp (negLaplacianCLM V).toLinearMap).comp
      (LinearEquiv.ofInjective (schwartzToL2 (V := V))
        (SchwartzMap.injective_toLp 2 (volume : Measure V))).symm.toLinearMap

/-! ### Maximal-domain (Fourier-side) form

Supporting unbounded-operator infrastructure copied verbatim (with its sorry-free
proofs) from `Brockian_fourier_lineDerivOp_sq.lean`, since `freeLaplacianMax`
cannot be stated without it. -/

section mul

variable (m : V → ℝ)

/-- The maximal domain of the multiplication operator by `m` inside `L²`
(from `Brockian_fourier_lineDerivOp_sq.lean`). -/
def mulDomain : Submodule ℂ (L2 V) where
  carrier := {u : L2 V | MemLp (fun x => (m x : ℂ) * (u : V → ℂ) x) 2 (volume : Measure V)}
  add_mem' := by
    intro u v hu hv
    refine (MemLp.add hu hv).ae_eq ?_
    filter_upwards [Lp.coeFn_add u v] with x hx
    simp only [Pi.add_apply] at hx ⊢
    rw [hx]; ring
  zero_mem' := by
    refine (MemLp.zero (p := 2) (μ := (volume : Measure V)) (ε := ℂ)).ae_eq ?_
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure V)] with x hx
    simp
  smul_mem' := by
    intro c u hu
    refine (MemLp.const_smul hu c).ae_eq ?_
    filter_upwards [Lp.coeFn_smul c u] with x hx
    simp only [Pi.smul_apply, smul_eq_mul] at hx ⊢
    rw [hx]; ring

/-- The function underlying the multiplication operator. -/
def mulFun (u : mulDomain m) : L2 V := MemLp.toLp _ u.2

theorem coeFn_mulFun (u : mulDomain m) :
    ((mulFun m u : L2 V) : V → ℂ) =ᵐ[volume] fun x => (m x : ℂ) * ((u : L2 V) : V → ℂ) x :=
  MemLp.coeFn_toLp u.2

/-- The multiplication operator by a real-valued function `m`, as an unbounded
operator on `L²(V; ℂ)` with maximal domain
(from `Brockian_fourier_lineDerivOp_sq.lean`). -/
def mulOp : L2 V →ₗ.[ℂ] L2 V where
  domain := mulDomain m
  toFun :=
    { toFun := mulFun m
      map_add' := by
        intro u v
        refine Lp.ext ?_
        filter_upwards [coeFn_mulFun m (u + v), coeFn_mulFun m u, coeFn_mulFun m v,
          Lp.coeFn_add (mulFun m u) (mulFun m v), Lp.coeFn_add (u : L2 V) (v : L2 V)]
          with x h1 h2 h3 h4 h5
        simp only [Pi.add_apply] at *
        rw [h1, h4, h2, h3,
          show ((u + v : mulDomain m) : L2 V) = (u : L2 V) + (v : L2 V) from rfl, h5]
        ring
      map_smul' := by
        intro c u
        refine Lp.ext ?_
        filter_upwards [coeFn_mulFun m (c • u), coeFn_mulFun m u,
          Lp.coeFn_smul c (mulFun m u), Lp.coeFn_smul c (u : L2 V)] with x h1 h2 h3 h4
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply] at *
        rw [h1, h3, h2,
          show ((c • u : mulDomain m) : L2 V) = c • (u : L2 V) from rfl, h4]
        ring }

end mul

section conj

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The conjugate `U⁻¹ ∘ T ∘ U` of an unbounded operator `T` by a unitary `U`
(from `Brockian_fourier_lineDerivOp_sq.lean`). -/
def conjPMap (U : E ≃ₗᵢ[𝕜] E) (T : E →ₗ.[𝕜] E) : E →ₗ.[𝕜] E where
  domain := T.domain.comap (U.toLinearEquiv : E →ₗ[𝕜] E)
  toFun := ((U.symm.toLinearEquiv : E →ₗ[𝕜] E) ∘ₗ T.toFun) ∘ₗ
    ((U.toLinearEquiv : E →ₗ[𝕜] E).restrict
      (p := T.domain.comap (U.toLinearEquiv : E →ₗ[𝕜] E)) (q := T.domain) (fun _ hx => hx))

end conj

/-- The Fourier transform as a unitary of `L²(V; ℂ)` (Plancherel's theorem). -/
abbrev fourierU (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] :
    L2 V ≃ₗᵢ[ℂ] L2 V := Lp.fourierTransformₗᵢ V ℂ

/-- The free Laplacian with its MAXIMAL domain: the conjugate under the Fourier
transform of multiplication by the symbol `4π²‖ξ‖²` (canonical form of the
`freeLaplacian` of `Brockian_fourier_lineDerivOp_sq.lean`).  A genuinely different
operator from `freeLaplacian` — its domain is the full multiplier domain — hence
the distinct name; essential self-adjointness of `freeLaplacian` identifies
`freeLaplacianMax` with the closure of `freeLaplacian` (fleet targets below). -/
def freeLaplacianMax : L2 V →ₗ.[ℂ] L2 V :=
  conjPMap (fourierU V) (mulOp freeSymbol)

-- FLEET TARGET: theorem negLaplacianCLM_apply_real (f : 𝓢(ℝ, ℂ)) :
--   negLaplacianCLM ℝ f = -((SchwartzMap.derivCLM ℂ ℂ ∘L SchwartzMap.derivCLM ℂ ℂ) f)
--   (bridges the `V = ℝ` island `Brockian_FreeLaplacianPlancherel_...via_plancherel.lean`:
--    on ℝ, `Δ = deriv ∘ deriv`; via `SchwartzMap.laplacian_eq_sum` over the
--    one-element orthonormal basis of ℝ).
-- FLEET TARGET: theorem negLaplacianCLM_eq_sum_lineDeriv (d : ℕ)
--     (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) :
--   negLaplacianCLM (EuclideanSpace ℝ (Fin d)) f
--     = -(∑ i : Fin d,
--         (LineDeriv.lineDerivOpCLM ℂ 𝓢(EuclideanSpace ℝ (Fin d), ℂ)
--           (EuclideanSpace.single i (1 : ℝ))) ∘L
--         (LineDeriv.lineDerivOpCLM ℂ 𝓢(EuclideanSpace ℝ (Fin d), ℂ)
--           (EuclideanSpace.single i (1 : ℝ)))) f
--   (bridges `Brockian_Weyl_FreeLaplacian2_norm_sub_I_smul_sq.lean`; via
--    `SchwartzMap.laplacian_eq_sum` over the standard orthonormal basis).
-- FLEET TARGET: theorem fourier_negLaplacianCLM (f : 𝓢(V, ℂ)) (ξ : V) :
--   𝓕 (negLaplacianCLM V f) ξ = (freeSymbol ξ : ℂ) * 𝓕 f ξ
--   (the symbol computation, proved independently in three islands — canonical once).
-- FLEET TARGET: theorem freeLaplacian_le_freeLaplacianMax :
--   (freeLaplacian (V := V)) ≤ (freeLaplacianMax (V := V))
--   (the Schwartz-domain operator is a restriction of the maximal one; this is the
--    statement gluing variant 1 to variants 3/5).
-- FLEET TARGET: theorem isSelfAdjoint_freeLaplacianMax :
--   (freeLaplacianMax (V := V)).IsSelfAdjoint
--   (restates the main theorem of `Brockian_fourier_lineDerivOp_sq.lean` /
--    `Brockian_FreeLaplacianPlancherel_...` in canonical vocabulary: multiplication by
--    a real symbol is self-adjoint on its maximal domain, and conjugation by the
--    Plancherel unitary preserves self-adjointness).
-- FLEET TARGET: theorem freeLaplacian_essentiallySelfAdjoint :
--   -- closure (freeLaplacian (V := V)) is self-adjoint, equivalently
--   -- (freeLaplacian (V := V)).closure = freeLaplacianMax (V := V)
--   True  -- placeholder statement shape; restates the main theorems of the two
--         -- `essentiallySelfAdjoint` islands against the canonical operators.
-- FLEET TARGET: theorem freeLaplacian_domain_dense :
--   Dense ((schwartzSubmodule (V := V) : Submodule ℂ (L2 V)) : Set (L2 V))
--   (from `SchwartzMap.denseRange_toLpCLM`; needed by every adjoint statement above).

end freeLaplacian

end BrockianCore
