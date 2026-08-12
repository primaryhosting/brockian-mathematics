import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
# Li's criterion (finite / Bombieri–Lagarias core)

Li's criterion states that the Riemann Hypothesis is equivalent to the non-negativity of the
Li coefficients
`λ_n = ∑_ρ (1 - (1 - 1/ρ)^n)`,
the sum being over the non-trivial zeros of the Riemann zeta function (equivalently, the zeros
of the completed function `ξ`), counted with multiplicity.

This file formalises and proves the arithmetic-free *core* of the criterion: the equivalence
for an arbitrary **finite** family of non-zero complex numbers `ρ i` that is closed under the
functional-equation symmetry `ρ ↦ 1 - ρ`.  For such a family,

* every `ρ i` lies on the critical line `Re ρ = 1/2`

  if and only if

* all the Li coefficients `λ_n`, `n ≥ 1`, have non-negative real part.

This is exactly the statement of Li's criterion with the zero multiset of `ξ` replaced by a
finite symmetric multiset; the two ingredients that are special to `ξ` (the Hadamard product,
which produces the zero multiset and the convergence of the defining series) are not part of
this statement.

The mathematical content proved here is:

* the *Möbius dictionary* `‖1 - 1/ρ‖ = 1 ↔ Re ρ = 1/2` and `1 < ‖1 - 1/ρ‖ ↔ Re ρ < 1/2`
  (`Frontier.norm_one_sub_inv_eq_one_iff`, `Frontier.one_lt_norm_one_sub_inv_iff`);
* the easy direction, that a zero on the critical line contributes a non-negative real part
  to every `λ_n`;
* the hard direction, a Diophantine/recurrence argument (the finite analogue of the
  Bombieri–Lagarias argument): if some `‖z i‖ > 1`, then the power sums `∑ i, Re (z i ^ n)`
  are unbounded above, because arbitrarily large powers `n` can be chosen so that all the
  `z i ^ n` point in almost the same direction as the positive real axis.
-/

namespace Frontier

open Complex Filter

/-! ### The Möbius dictionary -/

/-- The basic identity behind Li's criterion: `‖1 - 1/ρ‖` compares with `1` exactly as
`Re ρ` compares with `1/2`. -/
theorem norm_one_sub_inv_sq_sub_one (ρ : ℂ) (hρ : ρ ≠ 0) :
    (‖1 - 1 / ρ‖ ^ 2 - 1) * ‖ρ‖ ^ 2 = 1 - 2 * ρ.re := by
  have hn : ‖ρ‖ ≠ 0 := by simpa using hρ
  have hs : ρ.re ^ 2 + ρ.im ^ 2 ≠ 0 := by
    have : Complex.normSq ρ ≠ 0 := by simpa [Complex.normSq_eq_zero] using hρ
    simpa [Complex.normSq_apply, sq] using this
  have h1 : ‖1 - 1 / ρ‖ = ‖ρ - 1‖ / ‖ρ‖ := by
    rw [← norm_div]; congr 1; field_simp
  rw [h1, div_pow, Complex.sq_norm, Complex.sq_norm, Complex.normSq_sub]
  simp only [Complex.normSq_apply, map_one, mul_one]
  field_simp
  ring

/-- A non-zero `ρ` lies on the critical line iff `1 - 1/ρ` lies on the unit circle. -/
theorem norm_one_sub_inv_eq_one_iff (ρ : ℂ) (hρ : ρ ≠ 0) :
    ‖1 - 1 / ρ‖ = 1 ↔ ρ.re = 1 / 2 := by
  have hs : (0 : ℝ) < ‖ρ‖ ^ 2 := by positivity
  have hk := norm_one_sub_inv_sq_sub_one ρ hρ
  have hnn : (0 : ℝ) ≤ ‖1 - 1 / ρ‖ := norm_nonneg _
  set a := ‖1 - 1 / ρ‖ with ha
  constructor
  · intro h
    rw [h] at hk
    simp at hk
    linarith
  · intro h
    have h2 : (a ^ 2 - 1) * ‖ρ‖ ^ 2 = 0 := by rw [hk, h]; ring
    have h3 : a ^ 2 = 1 := by
      rcases mul_eq_zero.1 h2 with h' | h'
      · linarith
      · exact absurd h' (by positivity)
    nlinarith

/-- A non-zero `ρ` lies strictly left of the critical line iff `1 - 1/ρ` lies strictly outside
the unit circle. -/
theorem one_lt_norm_one_sub_inv_iff (ρ : ℂ) (hρ : ρ ≠ 0) :
    1 < ‖1 - 1 / ρ‖ ↔ ρ.re < 1 / 2 := by
  have hs : (0 : ℝ) < ‖ρ‖ ^ 2 := by positivity
  have hk := norm_one_sub_inv_sq_sub_one ρ hρ
  have hnn : (0 : ℝ) ≤ ‖1 - 1 / ρ‖ := norm_nonneg _
  set a := ‖1 - 1 / ρ‖ with ha
  constructor
  · intro h
    have h1 : 0 < a ^ 2 - 1 := by nlinarith
    nlinarith
  · intro h
    have h1 : 0 < (a ^ 2 - 1) * ‖ρ‖ ^ 2 := by rw [hk]; linarith
    have h2 : 0 < a ^ 2 - 1 := by nlinarith
    nlinarith

/-! ### A recurrence lemma on the torus -/

/-- Simultaneous recurrence: for finitely many complex numbers of modulus one there is a
positive exponent `n` making all the powers `u i ^ n` uniformly close to `1`. -/
theorem exists_pow_sub_one_norm_le {ι : Type*} [Fintype ι] (u : ι → ℂ) (hu : ∀ i, ‖u i‖ = 1)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ, 1 ≤ n ∧ ∀ i, ‖u i ^ n - 1‖ ≤ δ := by
  classical
  set x : ℕ → (ι → ℂ) := fun n i => u i ^ n with hx
  have hmem : ∀ n, x n ∈ (Metric.closedBall (0 : ι → ℂ) 1) := by
    intro n
    rw [Metric.mem_closedBall, dist_pi_le_iff (by norm_num)]
    intro i
    simp [hx, dist_eq_norm, norm_pow, hu i]
  obtain ⟨a, -, ph, hph, hconv⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hmem
  have hcauchy : CauchySeq (x ∘ ph) := hconv.cauchySeq
  rw [Metric.cauchySeq_iff] at hcauchy
  obtain ⟨N, hN⟩ := hcauchy δ hδ
  have hlt : dist ((x ∘ ph) (N + 1)) ((x ∘ ph) N) < δ := hN (N + 1) (by omega) N (by omega)
  set p := ph N
  set q := ph (N + 1)
  have hpq : p < q := hph (by omega)
  refine ⟨q - p, by omega, ?_⟩
  intro i
  have h2 : u i ^ q - u i ^ p = u i ^ p * (u i ^ (q - p) - 1) := by
    have : u i ^ q = u i ^ p * u i ^ (q - p) := by rw [← pow_add]; congr 1; omega
    rw [this]; ring
  have h3 : ‖u i ^ q - u i ^ p‖ = ‖u i ^ (q - p) - 1‖ := by
    rw [h2, norm_mul, norm_pow, hu i, one_pow, one_mul]
  calc ‖u i ^ (q - p) - 1‖ = ‖x q i - x p i‖ := h3.symm
    _ ≤ ‖x q - x p‖ := by
        have := dist_le_pi_dist (x q) (x p) i
        rw [dist_eq_norm, dist_eq_norm] at this
        exact this
    _ ≤ δ := by rw [← dist_eq_norm]; exact le_of_lt hlt

/-- `‖u ^ (m * n) - 1‖ ≤ m * ‖u ^ n - 1‖` for `u` of modulus one. -/
theorem norm_pow_mul_sub_one_le (u : ℂ) (hu : ‖u‖ = 1) (n m : ℕ) :
    ‖u ^ (m * n) - 1‖ ≤ m * ‖u ^ n - 1‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hstep : u ^ ((m + 1) * n) - 1 = u ^ n * (u ^ (m * n) - 1) + (u ^ n - 1) := by
        have : u ^ ((m + 1) * n) = u ^ n * u ^ (m * n) := by
          rw [← pow_add]; congr 1; ring
        rw [this]; ring
      have hnorm : ‖u ^ n‖ = 1 := by rw [norm_pow, hu, one_pow]
      calc ‖u ^ ((m + 1) * n) - 1‖
          ≤ ‖u ^ n * (u ^ (m * n) - 1)‖ + ‖u ^ n - 1‖ := by
            rw [hstep]; exact norm_add_le _ _
        _ = ‖u ^ (m * n) - 1‖ + ‖u ^ n - 1‖ := by rw [norm_mul, hnorm, one_mul]
        _ ≤ m * ‖u ^ n - 1‖ + ‖u ^ n - 1‖ := by linarith [ih]
        _ = ((m : ℝ) + 1) * ‖u ^ n - 1‖ := by ring
        _ = ((m + 1 : ℕ) : ℝ) * ‖u ^ n - 1‖ := by push_cast; ring

/-- The recurrence lemma with arbitrarily large exponents. -/
theorem exists_large_pow_sub_one_norm_le {ι : Type*} [Fintype ι] (u : ι → ℂ)
    (hu : ∀ i, ‖u i‖ = 1) {δ : ℝ} (hδ : 0 < δ) (N₀ : ℕ) :
    ∃ n : ℕ, N₀ ≤ n ∧ 1 ≤ n ∧ ∀ i, ‖u i ^ n - 1‖ ≤ δ := by
  classical
  set M : ℕ := max N₀ 1 with hM
  have hMpos : 0 < M := by positivity
  have hδ' : 0 < δ / M := by
    have : (0 : ℝ) < M := by exact_mod_cast hMpos
    positivity
  obtain ⟨n₁, hn₁, hle⟩ := exists_pow_sub_one_norm_le u hu hδ'
  refine ⟨M * n₁, ?_, ?_, ?_⟩
  · calc N₀ ≤ M := le_max_left _ _
      _ = M * 1 := by ring
      _ ≤ M * n₁ := Nat.mul_le_mul_left M hn₁
  · exact Nat.one_le_iff_ne_zero.2 (by positivity)
  · intro i
    have hMR : (0 : ℝ) < M := by exact_mod_cast hMpos
    calc ‖u i ^ (M * n₁) - 1‖ ≤ (M : ℝ) * ‖u i ^ n₁ - 1‖ :=
          norm_pow_mul_sub_one_le (u i) (hu i) n₁ M
      _ ≤ (M : ℝ) * (δ / M) := by
          exact mul_le_mul_of_nonneg_left (hle i) (le_of_lt hMR)
      _ = δ := by field_simp

/-! ### Unboundedness of power sums -/

/-- If one of finitely many complex numbers has modulus `> 1`, then the real parts of the
power sums `∑ i, Re (z i ^ n)` are unbounded above. -/
theorem exists_lt_sum_pow_re {ι : Type*} [Fintype ι] (z : ι → ℂ) (i₀ : ι) (hi₀ : 1 < ‖z i₀‖)
    (C : ℝ) : ∃ n : ℕ, 1 ≤ n ∧ C < ∑ i, (z i ^ n).re := by
  classical
  set u : ι → ℂ := fun i => if z i = 0 then 1 else z i / (‖z i‖ : ℂ) with hu_def
  have hu : ∀ i, ‖u i‖ = 1 := by
    intro i
    by_cases h : z i = 0
    · simp [hu_def, h]
    · have hz : (‖z i‖ : ℝ) ≠ 0 := by simpa using h
      simp [hu_def, h, hz]
  have hfac : ∀ (i : ι) (n : ℕ), z i ^ n = ((‖z i‖ : ℂ)) ^ n * u i ^ n := by
    intro i n
    by_cases h : z i = 0
    · simp [hu_def, h]
    · have hz : ((‖z i‖ : ℂ)) ≠ 0 := by
        simpa [Complex.ofReal_eq_zero] using (norm_ne_zero_iff.2 h)
      rw [← mul_pow]
      congr 1
      simp only [hu_def, h, if_false]
      field_simp
  -- choose a threshold exponent
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, max C 0 * 2 < ‖z i₀‖ ^ N₀ := pow_unbounded_of_one_lt _ hi₀
  obtain ⟨n, hnN, hn1, hclose⟩ :=
    exists_large_pow_sub_one_norm_le u hu (δ := (1 : ℝ) / 2) (by norm_num) N₀
  refine ⟨n, hn1, ?_⟩
  -- each term has real part at least ‖z i‖ ^ n / 2
  have hterm : ∀ i, ‖z i‖ ^ n / 2 ≤ (z i ^ n).re := by
    intro i
    have h1 : (1 : ℝ) / 2 ≤ (u i ^ n).re := by
      have h2 : (1 - u i ^ n).re ≤ ‖1 - u i ^ n‖ := Complex.re_le_norm _
      have h3 : ‖1 - u i ^ n‖ = ‖u i ^ n - 1‖ := by rw [norm_sub_rev]
      have := hclose i
      simp only [Complex.sub_re, Complex.one_re] at h2
      linarith [h2, h3 ▸ (hclose i)]
    have h4 : (z i ^ n).re = ‖z i‖ ^ n * (u i ^ n).re := by
      rw [hfac i n, ← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im]
      ring
    have h5 : (0 : ℝ) ≤ ‖z i‖ ^ n := by positivity
    rw [h4]
    nlinarith
  have hnonneg : ∀ i ∈ Finset.univ, 0 ≤ (z i ^ n).re := by
    intro i _
    have := hterm i
    have h5 : (0 : ℝ) ≤ ‖z i‖ ^ n := by positivity
    linarith
  have hsum : (z i₀ ^ n).re ≤ ∑ i, (z i ^ n).re :=
    Finset.single_le_sum hnonneg (Finset.mem_univ i₀)
  have hmono : ‖z i₀‖ ^ N₀ ≤ ‖z i₀‖ ^ n :=
    pow_le_pow_right₀ (le_of_lt hi₀) hnN
  have hCle : C ≤ max C 0 := le_max_left _ _
  have := hterm i₀
  nlinarith [le_max_right C (0:ℝ)]

/-! ### The Li coefficients and the criterion -/

/-- The `n`-th Li coefficient of a finite family of (non-zero) complex numbers `ρ`:
`λ_n = ∑_i (1 - (1 - 1/ρ i)^n)`. -/
noncomputable def liCoeff {ι : Type*} [Fintype ι] (ρ : ι → ℂ) (n : ℕ) : ℂ :=
  ∑ i, (1 - (1 - 1 / ρ i) ^ n)

/-- **Li's criterion (finite symmetric form).**

Let `ρ : ι → ℂ` be a finite family of non-zero complex numbers ("the zeros"), closed under
the functional-equation symmetry `ρ ↦ 1 - ρ`, in the sense that there is a map `σ : ι → ι`
with `ρ (σ i) = 1 - ρ i`.  Then all the `ρ i` lie on the critical line `Re ρ = 1/2` if and
only if all the Li coefficients `λ_n`, `n ≥ 1`, have non-negative real part.

This is the arithmetic-free core of Li's criterion for the Riemann Hypothesis: with `ρ`
ranging over the non-trivial zeros of the Riemann zeta function (which are non-zero and are
permuted by `ρ ↦ 1 - ρ`), the left-hand side is the Riemann Hypothesis and the right-hand
side is the non-negativity of Li's coefficients. -/
theorem RH_Li_criterion {ι : Type*} [Fintype ι] (ρ : ι → ℂ) (hρ : ∀ i, ρ i ≠ 0)
    (σ : ι → ι) (hσ : ∀ i, ρ (σ i) = 1 - ρ i) :
    (∀ i, (ρ i).re = 1 / 2) ↔ ∀ n : ℕ, 1 ≤ n → 0 ≤ (liCoeff ρ n).re := by
  classical
  constructor
  · -- easy direction: each summand has non-negative real part
    intro hline n _
    rw [liCoeff, Complex.re_sum]
    refine Finset.sum_nonneg ?_
    intro i _
    have hnorm : ‖1 - 1 / ρ i‖ = 1 :=
      (norm_one_sub_inv_eq_one_iff (ρ i) (hρ i)).2 (hline i)
    have h1 : ((1 - 1 / ρ i) ^ n).re ≤ ‖(1 - 1 / ρ i) ^ n‖ := Complex.re_le_norm _
    have h2 : ‖(1 - 1 / ρ i) ^ n‖ = 1 := by rw [norm_pow, hnorm, one_pow]
    simp only [Complex.sub_re, Complex.one_re]
    linarith [h2 ▸ h1]
  · -- hard direction, by contraposition
    intro hpos
    by_contra hcon
    push_neg at hcon
    obtain ⟨i₁, hi₁⟩ := hcon
    -- find an index strictly to the left of the critical line
    obtain ⟨j, hj⟩ : ∃ j, (ρ j).re < 1 / 2 := by
      rcases lt_or_gt_of_ne hi₁ with h | h
      · exact ⟨i₁, h⟩
      · refine ⟨σ i₁, ?_⟩
        rw [hσ i₁]
        simp only [Complex.sub_re, Complex.one_re]
        linarith
    set z : ι → ℂ := fun i => 1 - 1 / ρ i with hz
    have hzj : 1 < ‖z j‖ := (one_lt_norm_one_sub_inv_iff (ρ j) (hρ j)).2 hj
    obtain ⟨n, hn1, hgt⟩ := exists_lt_sum_pow_re z j hzj (Fintype.card ι : ℝ)
    have hre : (liCoeff ρ n).re = (Fintype.card ι : ℝ) - ∑ i, (z i ^ n).re := by
      rw [liCoeff, Complex.re_sum]
      simp only [Complex.sub_re, Complex.one_re, hz]
      rw [Finset.sum_sub_distrib]
      simp [Finset.card_univ]
    have := hpos n hn1
    rw [hre] at this
    linarith

/-- **Li's criterion for a finite symmetric family of non-trivial zeta zeros.**

If `ρ : ι → ℂ` is a finite family of zeros of the Riemann zeta function inside the critical
strip `0 < Re ρ < 1`, closed under `ρ ↦ 1 - ρ` (the symmetry satisfied by the full zero set,
by the functional equation), then all of them lie on the critical line if and only if all the
associated Li coefficients `λ_n`, `n ≥ 1`, have non-negative real part.

Taking `ι` to index *all* non-trivial zeros would give Li's criterion for the Riemann
Hypothesis itself; that statement additionally requires the Hadamard factorisation of the
completed zeta function, which is not used (nor available) here.

(The hypothesis `hzero` that the `ρ i` are zeros of `ζ` is recorded to make the statement one
about zeta zeros, but it is not needed for the proof: only `0 < Re ρ i` is used, to guarantee
`ρ i ≠ 0`.) -/
theorem RH_Li_criterion_zeta {ι : Type*} [Fintype ι] (ρ : ι → ℂ)
    (hzero : ∀ i, riemannZeta (ρ i) = 0) (hstrip : ∀ i, 0 < (ρ i).re ∧ (ρ i).re < 1)
    (σ : ι → ι) (hσ : ∀ i, ρ (σ i) = 1 - ρ i) :
    (∀ i, (ρ i).re = 1 / 2) ↔ ∀ n : ℕ, 1 ≤ n → 0 ≤ (liCoeff ρ n).re := by
  refine RH_Li_criterion ρ (fun i h => ?_) σ hσ
  have := (hstrip i).1
  rw [h] at this
  simp at this

/-- Sanity check: the criterion is not vacuous.  For the symmetric pair `{1/4, 3/4}`, which is
off the critical line, the second Li coefficient is negative. -/
example : ((liCoeff (![(1 / 4 : ℂ), 3 / 4]) 2).re) < 0 := by
  simp [liCoeff, Fin.sum_univ_two]
  norm_num

end Frontier

