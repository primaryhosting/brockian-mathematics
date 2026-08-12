/-
# Donsker Invariance
Category: Frontier Math
Target: Math2.donsker_invariance
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib
import RequestProject.Donsker.Defs
import RequestProject.Donsker.CharFun
import RequestProject.Donsker.CLT
import RequestProject.Donsker.Tight
import RequestProject.Donsker.Levy

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

set_option grind.warning false

open MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace

namespace Math2

/-- **Donsker's invariance principle** (convergence of the finite-dimensional distributions).

Let `μ` be the law of a centered step with unit variance, let `S_m` be the associated random walk
with i.i.d. steps (the steps being the coordinates of `ℕ → ℝ` under the product measure
`Math2.iidLaw μ`), and let `W_n(u) = S_{⌊n u⌋} / √n` be the rescaled walk.

Then, for any finite set of times `t 0 ≤ t 1 ≤ … ≤ t (k-1)`, the law `Math2.walkLaw μ t k n` of
the random vector `(W_n(t 0), …, W_n(t (k-1)))` converges weakly, as `n → ∞`, to the law
`Math2.bmLaw t k` of `(B_{t 0}, …, B_{t (k-1)})`, where `B` is a Brownian motion.  Weak
convergence is expressed as convergence of the integrals of all bounded continuous functions.

The limit does not depend on the step distribution `μ` (only on its mean and variance): this is
the invariance in Donsker's invariance principle.  That `Math2.bmLaw t k` really is the
finite-dimensional distribution of Brownian motion is the content of
`Math2.charFun_bmLaw_eq`: it is the centered Gaussian law with covariance
`min (t i) (t j)`. -/
theorem donsker_invariance {k : ℕ} (t : ℕ → ℝ) (ht : Monotone t) (ht0 : 0 ≤ t 0)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hint : Integrable (fun x ↦ x ^ 2) μ)
    (hmean : ∫ x, x ∂μ = 0) (hvar : ∫ x, x ^ 2 ∂μ = 1)
    (f : BoundedContinuousFunction (EuclideanSpace ℝ (Fin k)) ℝ) :
    Tendsto (fun n ↦ ∫ x, f x ∂(walkLaw μ t k n)) atTop (𝓝 (∫ x, f x ∂(bmLaw t k))) :=
  tendsto_integral_of_tendsto_charFun (fun n ↦ walkLaw μ t k n) (bmLaw t k)
    (isTightMeasureSet_walkLaw μ hint hmean hvar ht ht0)
    (fun s ↦ tendsto_charFun_walkLaw μ hint hmean hvar ht ht0 s) f

end Math2

import RequestProject.Donsker.Defs

/-!
# Tightness of the laws of the rescaled random walk

The second moment of the rescaled walk at time `t j` is at most `t j + 1`, uniformly in `n`, so
the family of laws of the rescaled walk is tight.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal RealInnerProductSpace

namespace Math2

variable {k : ℕ} {t : ℕ → ℝ}

/-! ### Moments of the i.i.d. sequence -/

lemma memLp_eval (μ : Measure ℝ) [IsProbabilityMeasure μ] (hint : Integrable (fun x ↦ x ^ 2) μ)
    (i : ℕ) : MemLp (fun ω : ℕ → ℝ ↦ ω i) 2 (iidLaw μ) := by
  have hmap : (iidLaw μ).map (fun ω : ℕ → ℝ ↦ ω i) = μ := Measure.infinitePi_map_eval _ i
  have h : MemLp (id : ℝ → ℝ) 2 μ := by
    rw [memLp_two_iff_integrable_sq (by fun_prop)]
    simpa using hint
  rw [← hmap] at h
  exact (memLp_map_measure_iff aestronglyMeasurable_id
    (measurable_pi_apply i).aemeasurable).mp h

lemma indepFun_eval (μ : Measure ℝ) [IsProbabilityMeasure μ] {i j : ℕ} (hij : i ≠ j) :
    IndepFun (fun ω : ℕ → ℝ ↦ ω i) (fun ω : ℕ → ℝ ↦ ω j) (iidLaw μ) :=
  (iIndepFun_infinitePi (P := fun _ : ℕ ↦ μ) (X := fun _ : ℕ ↦ (id : ℝ → ℝ))
    (fun _ ↦ measurable_id)).indepFun hij

lemma integral_eval (μ : Measure ℝ) [IsProbabilityMeasure μ] (hmean : ∫ x, x ∂μ = 0) (i : ℕ) :
    ∫ ω, ω i ∂(iidLaw μ) = 0 := by
  have hmap : (iidLaw μ).map (fun ω : ℕ → ℝ ↦ ω i) = μ := Measure.infinitePi_map_eval _ i
  have h := integral_map (μ := iidLaw μ) (φ := fun ω : ℕ → ℝ ↦ ω i) (f := fun x : ℝ ↦ x)
    (measurable_pi_apply i).aemeasurable (by fun_prop)
  rw [hmap, hmean] at h
  exact h.symm

lemma variance_eval (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmean : ∫ x, x ∂μ = 0) (hvar : ∫ x, x ^ 2 ∂μ = 1) (i : ℕ) :
    Var[fun ω : ℕ → ℝ ↦ ω i; iidLaw μ] = 1 := by
  have hmap : (iidLaw μ).map (fun ω : ℕ → ℝ ↦ ω i) = μ := Measure.infinitePi_map_eval _ i
  rw [variance_of_integral_eq_zero (measurable_pi_apply i).aemeasurable
    (integral_eval μ hmean i)]
  have h := integral_map (μ := iidLaw μ) (φ := fun ω : ℕ → ℝ ↦ ω i) (f := fun x : ℝ ↦ x ^ 2)
    (measurable_pi_apply i).aemeasurable (by fun_prop)
  rw [hmap, hvar] at h
  exact h.symm

/-- The partial sums of the i.i.d. sequence are square integrable. -/
lemma memLp_partialSum (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable (fun x ↦ x ^ 2) μ) (m : ℕ) :
    MemLp (fun ω : ℕ → ℝ ↦ ∑ i ∈ Finset.range m, ω i) 2 (iidLaw μ) := by
  have hfun : (fun ω : ℕ → ℝ ↦ ∑ i ∈ Finset.range m, ω i)
      = ∑ i ∈ Finset.range m, (fun ω : ℕ → ℝ ↦ ω i) := by
    ext ω; simp
  rw [hfun]
  exact memLp_finset_sum' _ (fun i _ ↦ memLp_eval μ hint i)

/-- The second moment of the partial sum of `m` i.i.d. centered variables with unit variance
is `m`. -/
lemma integral_partialSum_sq (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable (fun x ↦ x ^ 2) μ) (hmean : ∫ x, x ∂μ = 0) (hvar : ∫ x, x ^ 2 ∂μ = 1)
    (m : ℕ) :
    ∫ ω, (∑ i ∈ Finset.range m, ω i) ^ 2 ∂(iidLaw μ) = m := by
  have hmem : ∀ i, MemLp (fun ω : ℕ → ℝ ↦ ω i) 2 (iidLaw μ) := memLp_eval μ hint
  have hzero : ∫ ω : ℕ → ℝ, (∑ i ∈ Finset.range m, ω i) ∂(iidLaw μ) = 0 := by
    rw [integral_finset_sum _ (fun i _ ↦ ((hmem i).integrable one_le_two))]
    simp [integral_eval μ hmean]
  have hvarsum : Var[fun ω : ℕ → ℝ ↦ ∑ i ∈ Finset.range m, ω i; iidLaw μ] = m := by
    have hfun : (fun ω : ℕ → ℝ ↦ ∑ i ∈ Finset.range m, ω i)
        = ∑ i ∈ Finset.range m, (fun ω : ℕ → ℝ ↦ ω i) := by
      ext ω; simp
    rw [hfun, IndepFun.variance_sum (fun i _ ↦ hmem i)
      (fun i _ j _ hij ↦ indepFun_eval μ hij)]
    simp [variance_eval μ hmean hvar]
  rw [← hvarsum, variance_of_integral_eq_zero
    ((memLp_partialSum μ hint m).aestronglyMeasurable.aemeasurable) hzero]

/-! ### The second moment of the rescaled walk -/

lemma norm_sq_euclidean (x : EuclideanSpace ℝ (Fin k)) : ‖x‖ ^ 2 = ∑ j : Fin k, (x j) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun j _ ↦ by positivity)]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [Real.norm_eq_abs, sq_abs]

lemma integrable_norm_sq_walkLaw (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable (fun x ↦ x ^ 2) μ) (n : ℕ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin k) ↦ ‖x‖ ^ 2) (walkLaw μ t k n) := by
  rw [walkLaw, integrable_map_measure (by fun_prop) (measurable_walkVec t k n).aemeasurable]
  simp only [Function.comp_def]
  have hfun : (fun ω : ℕ → ℝ ↦ ‖walkVec t k n ω‖ ^ 2)
      = fun ω ↦ ∑ j : Fin k,
        ((∑ i ∈ Finset.range (stepCount t n j), ω i) / Real.sqrt n) ^ 2 := by
    ext ω
    rw [norm_sq_euclidean]
    rfl
  rw [hfun]
  refine integrable_finset_sum _ fun j _ ↦ ?_
  have hsq : Integrable (fun ω : ℕ → ℝ ↦ (∑ i ∈ Finset.range (stepCount t n j), ω i) ^ 2)
      (iidLaw μ) := by
    rw [← memLp_two_iff_integrable_sq (memLp_partialSum μ hint _).aestronglyMeasurable]
    exact memLp_partialSum μ hint _
  have := hsq.div_const ((Real.sqrt n) ^ 2)
  refine this.congr ?_
  filter_upwards with ω
  rw [div_pow]

/-- The second moment of the rescaled walk vector. -/
lemma integral_norm_sq_walkLaw (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable (fun x ↦ x ^ 2) μ) (hmean : ∫ x, x ∂μ = 0) (hvar : ∫ x, x ^ 2 ∂μ = 1)
    (n : ℕ) :
    ∫ x, ‖x‖ ^ 2 ∂(walkLaw μ t k n) = ∑ j : Fin k, (stepCount t n j : ℝ) / n := by
  rw [walkLaw, integral_map (measurable_walkVec t k n).aemeasurable (by fun_prop)]
  have hfun : (fun ω : ℕ → ℝ ↦ ‖walkVec t k n ω‖ ^ 2)
      = fun ω ↦ ∑ j : Fin k,
        ((∑ i ∈ Finset.range (stepCount t n j), ω i) / Real.sqrt n) ^ 2 := by
    ext ω
    rw [norm_sq_euclidean]
    rfl
  rw [hfun]
  have hint' : ∀ j : Fin k, Integrable
      (fun ω : ℕ → ℝ ↦ ((∑ i ∈ Finset.range (stepCount t n j), ω i) / Real.sqrt n) ^ 2)
      (iidLaw μ) := by
    intro j
    have hsq : Integrable (fun ω : ℕ → ℝ ↦ (∑ i ∈ Finset.range (stepCount t n j), ω i) ^ 2)
        (iidLaw μ) := by
      rw [← memLp_two_iff_integrable_sq (memLp_partialSum μ hint _).aestronglyMeasurable]
      exact memLp_partialSum μ hint _
    refine (hsq.div_const ((Real.sqrt n) ^ 2)).congr ?_
    filter_upwards with ω
    rw [div_pow]
  rw [integral_finset_sum _ fun j _ ↦ hint' j]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hdiv : ∀ ω : ℕ → ℝ,
      ((∑ i ∈ Finset.range (stepCount t n j), ω i) / Real.sqrt n) ^ 2
        = (∑ i ∈ Finset.range (stepCount t n j), ω i) ^ 2 / n := by
    intro ω
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  simp only [hdiv]
  rw [integral_div, integral_partialSum_sq μ hint hmean hvar]

/-- The second moment of the rescaled walk vector is bounded uniformly in `n`. -/
lemma integral_sq_norm_walkLaw_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable (fun x ↦ x ^ 2) μ) (hmean : ∫ x, x ∂μ = 0) (hvar : ∫ x, x ^ 2 ∂μ = 1)
    (ht : Monotone t) (ht0 : 0 ≤ t 0) (n : ℕ) :
    ∫ x, ‖x‖ ^ 2 ∂(walkLaw μ t k n) ≤ ∑ j : Fin k, (t j + 1) := by
  rw [integral_norm_sq_walkLaw μ hint hmean hvar n]
  refine Finset.sum_le_sum fun j _ ↦ ?_
  have hnonneg : 0 ≤ t j := ht0.trans (ht (Nat.zero_le j))
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
    linarith
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_le_iff₀ hn0]
    have hfloor : ((stepCount t n j : ℕ) : ℝ) ≤ (n : ℝ) * t j :=
      Nat.floor_le (by positivity)
    nlinarith

/-! ### Tightness -/

/-- The laws of the rescaled random walk form a tight family. -/
theorem isTightMeasureSet_walkLaw (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable (fun x ↦ x ^ 2) μ) (hmean : ∫ x, x ∂μ = 0) (hvar : ∫ x, x ^ 2 ∂μ = 1)
    (ht : Monotone t) (ht0 : 0 ≤ t 0) :
    IsTightMeasureSet {walkLaw μ t k n | n : ℕ} := by
  set C := ∑ j : Fin k, (t j + 1) with hC
  have hC0 : 0 ≤ C := by
    refine Finset.sum_nonneg fun j _ ↦ ?_
    have : 0 ≤ t j := ht0.trans (ht (Nat.zero_le j))
    linarith
  refine isTightMeasureSet_of_tendsto_measure_norm_gt ?_
  have hbound : ∀ r : ℝ, 0 < r →
      (⨆ ν ∈ {walkLaw μ t k n | n : ℕ}, ν {x : EuclideanSpace ℝ (Fin k) | r < ‖x‖})
        ≤ ENNReal.ofReal (C / r ^ 2) := by
    intro r hr
    refine iSup₂_le ?_
    rintro ν ⟨n, rfl⟩
    have hmono : {x : EuclideanSpace ℝ (Fin k) | r < ‖x‖}
        ⊆ {x : EuclideanSpace ℝ (Fin k) | r ^ 2 ≤ ‖x‖ ^ 2} := by
      intro x hx
      simp only [Set.mem_setOf_eq] at hx ⊢
      nlinarith [norm_nonneg x]
    have hmarkov : r ^ 2 * (walkLaw μ t k n).real
        {x : EuclideanSpace ℝ (Fin k) | r ^ 2 ≤ ‖x‖ ^ 2} ≤ C := by
      refine le_trans (mul_meas_ge_le_integral_of_nonneg
        (ae_of_all _ fun x ↦ by positivity) (integrable_norm_sq_walkLaw μ hint n) (r ^ 2)) ?_
      exact integral_sq_norm_walkLaw_le μ hint hmean hvar ht ht0 n
    have hreal : (walkLaw μ t k n).real {x : EuclideanSpace ℝ (Fin k) | r < ‖x‖}
        ≤ C / r ^ 2 := by
      refine le_trans (measureReal_mono hmono) ?_
      rw [le_div_iff₀ (by positivity)]
      linarith [hmarkov]
    calc (walkLaw μ t k n) {x : EuclideanSpace ℝ (Fin k) | r < ‖x‖}
        = ENNReal.ofReal ((walkLaw μ t k n).real {x : EuclideanSpace ℝ (Fin k) | r < ‖x‖}) := by
          rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
      _ ≤ ENNReal.ofReal (C / r ^ 2) := ENNReal.ofReal_le_ofReal hreal
  have hlim : Tendsto (fun r : ℝ ↦ ENNReal.ofReal (C / r ^ 2)) atTop (𝓝 0) := by
    have h : Tendsto (fun r : ℝ ↦ C / r ^ 2) atTop (𝓝 0) :=
      Tendsto.div_atTop tendsto_const_nhds (tendsto_pow_atTop two_ne_zero)
    have := (ENNReal.continuous_ofReal.tendsto 0).comp h
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun r ↦ zero_le _) ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr using hbound r hr

end Math2

import RequestProject.Donsker.CharFun

/-!
# The central limit estimate

We prove that the characteristic functions of the rescaled walk converge pointwise to the
characteristic function of the finite-dimensional distribution of Brownian motion.
-/

open MeasureTheory ProbabilityTheory Filter Complex
open scoped Topology ENNReal NNReal RealInnerProductSpace

namespace Math2

variable {k : ℕ} {t : ℕ → ℝ}

/-! ### Elementary estimates -/

/-- Elementary estimate: a product of complex numbers of modulus at most one depends on its
factors in a Lipschitz way. -/
lemma norm_prod_sub_prod_le {ι : Type*} (s : Finset ι) (f g : ι → ℂ)
    (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) (hg : ∀ i ∈ s, ‖g i‖ ≤ 1) :
    ‖∏ i ∈ s, f i - ∏ i ∈ s, g i‖ ≤ ∑ i ∈ s, ‖f i - g i‖ := by
  classical
  revert hf hg
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      intro hf hg
      have hf' : ∀ i ∈ s, ‖f i‖ ≤ 1 := fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
      have hg' : ∀ i ∈ s, ‖g i‖ ≤ 1 := fun i hi ↦ hg i (Finset.mem_insert_of_mem hi)
      have hprodf : ‖∏ i ∈ s, f i‖ ≤ 1 := by
        rw [norm_prod]
        exact Finset.prod_le_one (fun i _ ↦ norm_nonneg _) hf'
      have hga : ‖g a‖ ≤ 1 := hg a (Finset.mem_insert_self a s)
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
      have hsplit : f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i
          = (f a - g a) * (∏ i ∈ s, f i) + g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i) := by ring
      rw [hsplit]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
      have h1 : ‖f a - g a‖ * ‖∏ i ∈ s, f i‖ ≤ ‖f a - g a‖ * 1 :=
        mul_le_mul_of_nonneg_left hprodf (norm_nonneg _)
      have h2 : ‖g a‖ * ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ ≤ 1 * ∑ i ∈ s, ‖f i - g i‖ :=
        mul_le_mul hga (ih hf' hg') (norm_nonneg _) zero_le_one
      rw [mul_one] at h1
      rw [one_mul] at h2
      linarith

/-- Third order Taylor estimate for `exp (i r)`, valid for `|r| ≤ 2`. -/
lemma norm_exp_mul_I_sub_taylor_le_of_le (r : ℝ) (h : |r| ≤ 2) :
    ‖Complex.exp ((r : ℂ) * I) - (1 + (r : ℂ) * I - (r : ℂ) ^ 2 / 2)‖ ≤ |r| ^ 3 := by
  have hx : ‖((r : ℂ) * I)‖ = |r| := by simp
  have hI : ((r : ℂ) * I) ^ 2 = -(r : ℂ) ^ 2 := by rw [mul_pow, Complex.I_sq]; ring
  have hsum : ∑ m ∈ Finset.range 3, ((r : ℂ) * I) ^ m / (m.factorial : ℂ)
      = 1 + (r : ℂ) * I - (r : ℂ) ^ 2 / 2 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    push_cast
    rw [hI]
    ring
  have hb := Complex.exp_bound' (x := (r : ℂ) * I) (n := 3)
    (by rw [hx]; push_cast; linarith [abs_nonneg r])
  rw [hx, hsum] at hb
  refine hb.trans ?_
  have h6 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [h6]
  nlinarith [pow_nonneg (abs_nonneg r) 3]

/-- Third order Taylor estimate for `exp (i r)`, with a quadratic bound for large `r`. -/
lemma norm_exp_mul_I_sub_taylor_le (r : ℝ) :
    ‖Complex.exp ((r : ℂ) * I) - (1 + (r : ℂ) * I - (r : ℂ) ^ 2 / 2)‖
      ≤ min (|r| ^ 3) (4 * r ^ 2) := by
  have hnorm : ‖Complex.exp ((r : ℂ) * I)‖ = 1 := by simp [Complex.norm_exp_ofReal_mul_I]
  have hsq : |r| ^ 2 = r ^ 2 := sq_abs r
  have htriv : ‖Complex.exp ((r : ℂ) * I) - (1 + (r : ℂ) * I - (r : ℂ) ^ 2 / 2)‖
      ≤ 1 + (1 + |r| + r ^ 2 / 2) := by
    refine (norm_sub_le _ _).trans ?_
    rw [hnorm]
    gcongr
    refine (norm_sub_le _ _).trans ?_
    refine add_le_add ((norm_add_le _ _).trans ?_) ?_
    · simp
    · rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      simp
  rcases le_or_gt (|r|) 2 with hle | hgt
  · refine le_min (norm_exp_mul_I_sub_taylor_le_of_le r hle)
      ((norm_exp_mul_I_sub_taylor_le_of_le r hle).trans ?_)
    nlinarith [abs_nonneg r]
  · exact le_min (htriv.trans (by nlinarith [abs_nonneg r]))
      (htriv.trans (by nlinarith [abs_nonneg r]))

/-- Comparison of `exp (-a²/2)` with its first order expansion. -/
lemma norm_exp_sub_one_sub_le (a : ℝ) :
    ‖Complex.exp (-((a : ℂ) ^ 2) / 2) - (1 - (a : ℂ) ^ 2 / 2)‖ ≤ a ^ 4 := by
  have hcast : Complex.exp (-((a : ℂ) ^ 2) / 2) - (1 - (a : ℂ) ^ 2 / 2)
      = ((Real.exp (-(a ^ 2) / 2) - (1 - a ^ 2 / 2) : ℝ) : ℂ) := by
    have h : ((-(a ^ 2) / 2 : ℝ) : ℂ) = -((a : ℂ) ^ 2) / 2 := by push_cast; ring
    rw [← h, ← Complex.ofReal_exp]
    push_cast
    ring
  rw [hcast, Complex.norm_real, Real.norm_eq_abs]
  set y := a ^ 2 / 2 with hy
  have hy0 : 0 ≤ y := by positivity
  have hexp : Real.exp (-(a ^ 2) / 2) = Real.exp (-y) := by rw [hy]; ring_nf
  rw [hexp]
  rcases le_or_gt y 1 with h | h
  · have := Real.abs_exp_sub_one_sub_id_le (x := -y) (by rw [abs_neg, abs_of_nonneg hy0]; exact h)
    have habs : |Real.exp (-y) - (1 - y)| = |Real.exp (-y) - 1 - -y| := by ring_nf
    rw [habs]
    refine this.trans ?_
    have : y ^ 2 = a ^ 4 / 4 := by rw [hy]; ring
    nlinarith [pow_nonneg (sq_nonneg a) 2, sq_nonneg (a ^ 2)]
  · have h1 : 0 < Real.exp (-y) := Real.exp_pos _
    have h2 : Real.exp (-y) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith
    have h3 : |Real.exp (-y) - (1 - y)| ≤ y := by
      rw [abs_le]
      constructor <;> linarith
    have h4 : y ≤ y ^ 2 := by nlinarith
    have h5 : y ^ 2 = a ^ 4 / 4 := by rw [hy]; ring
    nlinarith [sq_nonneg (a ^ 2)]

/-! ### The Taylor error of a characteristic function -/

/-- The error term in the second order Taylor expansion of a characteristic function. -/
noncomputable def taylorErr (μ : Measure ℝ) (u : ℝ) : ℝ := ∫ x, min (u * |x| ^ 3) (4 * x ^ 2) ∂μ

lemma measurable_taylorErr_integrand (u : ℝ) :
    Measurable (fun x : ℝ ↦ min (u * |x| ^ 3) (4 * x ^ 2)) := by fun_prop

lemma integrable_taylorErr_integrand (μ : Measure ℝ) (hint : Integrable (fun x ↦ x ^ 2) μ)
    {u : ℝ} (hu : 0 ≤ u) : Integrable (fun x : ℝ ↦ min (u * |x| ^ 3) (4 * x ^ 2)) μ := by
  have hb : Integrable (fun x : ℝ ↦ 4 * x ^ 2) μ := hint.const_mul 4
  refine Integrable.mono hb (measurable_taylorErr_integrand u).aestronglyMeasurable ?_
  filter_upwards with x
  have h0 : 0 ≤ min (u * |x| ^ 3) (4 * x ^ 2) :=
    le_min (mul_nonneg hu (by positivity)) (by positivity)
  have h1 : min (u * |x| ^ 3) (4 * x ^ 2) ≤ 4 * x ^ 2 := min_le_right _ _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * x ^ 2)]
  exact h1

lemma taylorErr_nonneg (μ : Measure ℝ) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ taylorErr μ u :=
  integral_nonneg fun x ↦ le_min (mul_nonneg hu (by positivity)) (by positivity)

lemma taylorErr_mono (μ : Measure ℝ) (hint : Integrable (fun x ↦ x ^ 2) μ) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) : taylorErr μ u ≤ taylorErr μ v := by
  refine integral_mono (integrable_taylorErr_integrand μ hint hu)
    (integrable_taylorErr_integrand μ hint (hu.trans huv)) fun x ↦ ?_
  exact min_le_min (by nlinarith [abs_nonneg x, pow_nonneg (abs_nonneg x) 3]) le_rfl

/-- The Taylor error tends to `0` as `u → 0`, by dominated convergence. -/
lemma tendsto_taylorErr (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable (fun x ↦ x ^ 2) μ) (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n)
    (hu0 : Tendsto u atTop (𝓝 0)) :
    Tendsto (fun n ↦ taylorErr μ (u n)) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun n x ↦ min (u n * |x| ^ 3) (4 * x ^ 2)) (f := fun _ : ℝ ↦ (0 : ℝ))
    (bound := fun x ↦ 4 * x ^ 2)
    (fun n ↦ (measurable_taylorErr_integrand (u n)).aestronglyMeasurable)
    (hint.const_mul 4)
    (fun n ↦ by
      filter_upwards with x
      have h0 : 0 ≤ min (u n * |x| ^ 3) (4 * x ^ 2) :=
        le_min (mul_nonneg (hu n) (by positivity)) (by positivity)
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact min_le_right _ _)
    (by
      filter_upwards with x
      have hcube : Tendsto (fun n ↦ u n * |x| ^ 3) atTop (𝓝 0) := by
        simpa using hu0.mul_const (|x| ^ 3)
      refine squeeze_zero
        (fun n ↦ le_min (mul_nonneg (hu n) (by positivity)) (by positivity)) ?_ hcube
      exact fun n ↦ min_le_left _ _)
  simpa [taylorErr] using h

/-- Second order expansion of the characteristic function of a centered measure with unit
variance. -/
lemma norm_charFun_sub_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable (fun x ↦ x ^ 2) μ) (hmean : ∫ x, x ∂μ = 0) (hvar : ∫ x, x ^ 2 ∂μ = 1)
    (s : ℝ) :
    ‖charFun μ s - (1 - (s : ℂ) ^ 2 / 2)‖ ≤ s ^ 2 * taylorErr μ |s| := by
  have hfun : ∀ x : ℝ, (1 - (s * x) ^ 2 / 2 : ℝ) = 1 - s ^ 2 / 2 * x ^ 2 := fun x ↦ by ring
  have hint1 : Integrable (fun x : ℝ ↦ x) μ := by
    have h2 : Integrable (fun x : ℝ ↦ 1 + x ^ 2) μ := (integrable_const (1 : ℝ)).add hint
    refine Integrable.mono h2 (by fun_prop) ?_
    filter_upwards with x
    have h3 : ‖(1 : ℝ) + x ^ 2‖ = 1 + x ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [h3, Real.norm_eq_abs]
    nlinarith [sq_nonneg (|x| - 1), sq_abs x, abs_nonneg x]
  have hIexp : Integrable (fun x : ℝ ↦ Complex.exp (((s * x : ℝ) : ℂ) * I)) μ := by
    refine Integrable.mono (integrable_const (1 : ℝ)) (by fun_prop) ?_
    filter_upwards with x
    rw [Complex.norm_exp]
    simp
  have h0 : Integrable (fun x : ℝ ↦ (1 : ℝ) - s ^ 2 / 2 * x ^ 2) μ :=
    (integrable_const (1 : ℝ)).sub (hint.const_mul (s ^ 2 / 2))
  have hIa : Integrable (fun x : ℝ ↦ ((1 - (s * x) ^ 2 / 2 : ℝ) : ℂ)) μ := by
    simp only [hfun]
    exact h0.ofReal
  have hIb : Integrable (fun x : ℝ ↦ ((s * x : ℝ) : ℂ) * I) μ :=
    ((hint1.const_mul s).ofReal).mul_const I
  have hIab : Integrable
      (fun x : ℝ ↦ ((1 - (s * x) ^ 2 / 2 : ℝ) : ℂ) + ((s * x : ℝ) : ℂ) * I) μ := hIa.add hIb
  have e1 : ∫ x : ℝ, (((1 - (s * x) ^ 2 / 2 : ℝ) : ℂ) + ((s * x : ℝ) : ℂ) * I) ∂μ
      = 1 - (s : ℂ) ^ 2 / 2 := by
    rw [integral_add hIa hIb, integral_complex_ofReal, integral_mul_const,
      integral_complex_ofReal]
    have ha : ∫ x : ℝ, (1 - (s * x) ^ 2 / 2 : ℝ) ∂μ = 1 - s ^ 2 / 2 := by
      simp only [hfun]
      rw [integral_sub (integrable_const 1) (hint.const_mul (s ^ 2 / 2)), integral_const_mul, hvar]
      simp
    have hb : ∫ x : ℝ, (s * x : ℝ) ∂μ = 0 := by rw [integral_const_mul, hmean, mul_zero]
    rw [ha, hb]
    push_cast
    ring
  have hsplit : ∀ x : ℝ, (1 + ((s * x : ℝ) : ℂ) * I - ((s * x : ℝ) : ℂ) ^ 2 / 2)
      = ((1 - (s * x) ^ 2 / 2 : ℝ) : ℂ) + ((s * x : ℝ) : ℂ) * I := by
    intro x; push_cast; ring
  have hIfull : Integrable (fun x : ℝ ↦ Complex.exp (((s * x : ℝ) : ℂ) * I)
      - (1 + ((s * x : ℝ) : ℂ) * I - ((s * x : ℝ) : ℂ) ^ 2 / 2)) μ := by
    simp only [hsplit]
    exact hIexp.sub hIab
  have key : charFun μ s - (1 - (s : ℂ) ^ 2 / 2)
      = ∫ x : ℝ, (Complex.exp (((s * x : ℝ) : ℂ) * I)
          - (1 + ((s * x : ℝ) : ℂ) * I - ((s * x : ℝ) : ℂ) ^ 2 / 2)) ∂μ := by
    simp only [hsplit]
    rw [integral_sub hIexp hIab, e1, charFun_apply_real]
    congr 1
    exact congrArg _ (funext fun x ↦ by push_cast; ring_nf)
  rw [key]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hbound : ∀ x : ℝ, ‖Complex.exp (((s * x : ℝ) : ℂ) * I)
      - (1 + ((s * x : ℝ) : ℂ) * I - ((s * x : ℝ) : ℂ) ^ 2 / 2)‖
      ≤ s ^ 2 * min (|s| * |x| ^ 3) (4 * x ^ 2) := by
    intro x
    refine (norm_exp_mul_I_sub_taylor_le (s * x)).trans ?_
    have h1 : |s * x| ^ 3 = s ^ 2 * (|s| * |x| ^ 3) := by
      rw [abs_mul, mul_pow, show |s| ^ 3 = |s| ^ 2 * |s| by ring, sq_abs]
      ring
    have h2 : 4 * (s * x) ^ 2 = s ^ 2 * (4 * x ^ 2) := by ring
    rw [h1, h2, ← mul_min_of_nonneg _ _ (sq_nonneg s)]
  have hmin_int : Integrable (fun x : ℝ ↦ min (|s| * |x| ^ 3) (4 * x ^ 2)) μ :=
    integrable_taylorErr_integrand μ hint (abs_nonneg s)
  have hnorm_int : Integrable (fun x : ℝ ↦ ‖Complex.exp (((s * x : ℝ) : ℂ) * I)
      - (1 + ((s * x : ℝ) : ℂ) * I - ((s * x : ℝ) : ℂ) ^ 2 / 2)‖) μ :=
    hIfull.norm
  calc ∫ x : ℝ, ‖Complex.exp (((s * x : ℝ) : ℂ) * I)
        - (1 + ((s * x : ℝ) : ℂ) * I - ((s * x : ℝ) : ℂ) ^ 2 / 2)‖ ∂μ
      ≤ ∫ x : ℝ, s ^ 2 * min (|s| * |x| ^ 3) (4 * x ^ 2) ∂μ :=
        integral_mono hnorm_int (hmin_int.const_mul _) hbound
    _ = s ^ 2 * taylorErr μ |s| := by rw [integral_const_mul]; rfl

/-! ### Convergence of the characteristic functions -/

/-- Counting the indices below `m` inside `Finset.range M`, for `m ≤ M`. -/
lemma sum_range_indicator_lt {M m : ℕ} (h : m ≤ M) :
    ∑ i ∈ Finset.range M, (if i < m then (1 : ℝ) else 0) = m := by
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul, mul_one]
  congr 1
  have hfil : Finset.filter (fun i ↦ i < m) (Finset.range M) = Finset.range m := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun hi ↦ hi.2, fun hi ↦ ⟨hi.trans_le h, hi⟩⟩
  rw [hfil, Finset.card_range]

lemma abs_walkCoef_le (n : ℕ) (s : EuclideanSpace ℝ (Fin k)) (i : ℕ) :
    |walkCoef t k n s i| ≤ (∑ j : Fin k, |s j|) / Real.sqrt n := by
  rw [walkCoef, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  gcongr
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum fun j _ ↦ ?_
  split_ifs
  · exact le_rfl
  · simp

/-- For `u ≥ 0`, `⌊n u⌋ / n → u`. -/
lemma tendsto_stepCount_div (u : ℝ) (hu : 0 ≤ u) :
    Tendsto (fun n : ℕ ↦ (⌊(n : ℝ) * u⌋₊ : ℝ) / n) atTop (𝓝 u) := by
  have h := (tendsto_nat_floor_mul_div_atTop (R := ℝ) (a := u) hu).comp
    tendsto_natCast_atTop_atTop
  refine h.congr fun n ↦ ?_
  simp [Function.comp, mul_comm]

/-- The sum of the squares of the walk coefficients converges. -/
lemma tendsto_sum_sq_walkCoef (ht : Monotone t) (ht0 : 0 ≤ t 0)
    (s : EuclideanSpace ℝ (Fin k)) :
    Tendsto (fun n ↦ ∑ i ∈ Finset.range (stepCount t n k), walkCoef t k n s i ^ 2) atTop
      (𝓝 (∑ l ∈ Finset.range k, bmCoef t k s l ^ 2)) := by
  have hnonneg : ∀ j : ℕ, 0 ≤ t j := fun j ↦ ht0.trans (ht (Nat.zero_le j))
  have hle : ∀ (n : ℕ) (j : Fin k), stepCount t n j ≤ stepCount t n k := by
    intro n j
    apply Nat.floor_le_floor
    have h1 : t j ≤ t k := ht (le_of_lt j.isLt)
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  -- rewrite the sum of squares as a quadratic form in the step counts
  have hrewrite : ∀ n : ℕ, ∑ i ∈ Finset.range (stepCount t n k), walkCoef t k n s i ^ 2
      = ∑ j : Fin k, ∑ j' : Fin k,
          ((min (stepCount t n j) (stepCount t n j') : ℕ) : ℝ) / n * (s j * s j') := by
    intro n
    have hsq : ∀ i, walkCoef t k n s i ^ 2
        = (∑ j : Fin k, if i < stepCount t n j then s j else 0) ^ 2 / n := by
      intro i
      rw [walkCoef, div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    simp only [hsq]
    rw [← Finset.sum_div]
    have hexp : ∀ i, (∑ j : Fin k, if i < stepCount t n j then s j else 0) ^ 2
        = ∑ j : Fin k, ∑ j' : Fin k,
            ((if i < stepCount t n j then (1 : ℝ) else 0)
              * (if i < stepCount t n j' then (1 : ℝ) else 0)) * (s j * s j') := by
      intro i
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun j' _ ↦ ?_
      split_ifs <;> ring
    simp only [hexp]
    rw [Finset.sum_comm]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Finset.sum_comm, Finset.sum_div]
    refine Finset.sum_congr rfl fun j' _ ↦ ?_
    have hcard : ∑ i ∈ Finset.range (stepCount t n k),
        ((if i < stepCount t n j then (1 : ℝ) else 0)
          * (if i < stepCount t n j' then (1 : ℝ) else 0)) * (s j * s j')
        = ((min (stepCount t n j) (stepCount t n j') : ℕ) : ℝ) * (s j * s j') := by
      rw [← Finset.sum_mul]
      congr 1
      have : ∀ i, ((if i < stepCount t n j then (1 : ℝ) else 0)
          * (if i < stepCount t n j' then (1 : ℝ) else 0))
          = if i < min (stepCount t n j) (stepCount t n j') then (1 : ℝ) else 0 := by
        intro i
        by_cases h1 : i < stepCount t n j <;> by_cases h2 : i < stepCount t n j' <;>
          simp [h1, h2]
      simp only [this]
      exact sum_range_indicator_lt ((min_le_left _ _).trans (hle n j))
    rw [hcard]
    ring
  simp only [hrewrite]
  -- pass to the limit in each term
  have hterm : ∀ j j' : Fin k,
      Tendsto (fun n : ℕ ↦ ((min (stepCount t n j) (stepCount t n j') : ℕ) : ℝ) / n
        * (s j * s j')) atTop (𝓝 (min (t j) (t j') * (s j * s j'))) := by
    intro j j'
    have h1 := tendsto_stepCount_div (t j) (hnonneg j)
    have h2 := tendsto_stepCount_div (t j') (hnonneg j')
    have hmin : ∀ n : ℕ, ((min (stepCount t n j) (stepCount t n j') : ℕ) : ℝ) / n
        = min ((⌊(n : ℝ) * t j⌋₊ : ℝ) / n) ((⌊(n : ℝ) * t j'⌋₊ : ℝ) / n) := by
      intro n
      rw [stepCount, stepCount, Nat.cast_min,
        min_div_div_right (by positivity : (0 : ℝ) ≤ (n : ℝ))]
    simp only [hmin]
    exact (h1.min h2).mul_const _
  have hsum := tendsto_finset_sum (Finset.univ : Finset (Fin k))
    (fun j _ ↦ tendsto_finset_sum (Finset.univ : Finset (Fin k)) fun j' _ ↦ hterm j j')
  have heq : (∑ i : Fin k, ∑ j : Fin k, min (t i) (t j) * s i * s j)
      = ∑ j : Fin k, ∑ j' : Fin k, min (t j) (t j') * (s j * s j') :=
    Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun j' _ ↦ by ring
  rw [sum_sq_bmCoef k t ht ht0 s, heq]
  exact hsum

/-- **Central limit estimate**: the characteristic functions of the rescaled random walk converge
pointwise to the characteristic function of the finite-dimensional distribution of Brownian
motion. -/
theorem tendsto_charFun_walkLaw (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable (fun x ↦ x ^ 2) μ) (hmean : ∫ x, x ∂μ = 0) (hvar : ∫ x, x ^ 2 ∂μ = 1)
    (ht : Monotone t) (ht0 : 0 ≤ t 0) (s : EuclideanSpace ℝ (Fin k)) :
    Tendsto (fun n ↦ charFun (walkLaw μ t k n) s) atTop (𝓝 (charFun (bmLaw t k) s)) := by
  set S := ∑ j : Fin k, |s j| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ ↦ abs_nonneg _
  set A : ℕ → ℝ := fun n ↦ S / Real.sqrt n with hA
  have hA0 : ∀ n, 0 ≤ A n := fun n ↦ div_nonneg hS0 (Real.sqrt_nonneg _)
  have hAtend : Tendsto A atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  set V : ℕ → ℝ := fun n ↦ ∑ i ∈ Finset.range (stepCount t n k), walkCoef t k n s i ^ 2 with hV
  have hVtend : Tendsto V atTop (𝓝 (∑ l ∈ Finset.range k, bmCoef t k s l ^ 2)) :=
    tendsto_sum_sq_walkCoef ht ht0 s
  set G : ℕ → ℂ := fun n ↦ Complex.exp (-((V n : ℝ) : ℂ) / 2) with hG
  have hGtend : Tendsto G atTop (𝓝 (charFun (bmLaw t k) s)) := by
    rw [charFun_bmLaw]
    exact (Complex.continuous_exp.tendsto _).comp
      (((Complex.continuous_ofReal.tendsto _).comp hVtend).neg.div_const 2)
  have hprodG : ∀ n, G n = ∏ i ∈ Finset.range (stepCount t n k),
      Complex.exp (-((walkCoef t k n s i : ℂ)) ^ 2 / 2) := by
    intro n
    have hcast : ((V n : ℝ) : ℂ)
        = ∑ i ∈ Finset.range (stepCount t n k), ((walkCoef t k n s i : ℂ)) ^ 2 := by
      rw [hV]; push_cast; rfl
    rw [hG]
    simp only
    rw [hcast, neg_div, Finset.sum_div, ← Finset.sum_neg_distrib, Complex.exp_sum]
    exact Finset.prod_congr rfl fun i _ ↦ by ring_nf
  have hbound : ∀ n, ‖charFun (walkLaw μ t k n) s - G n‖
      ≤ V n * (taylorErr μ (A n) + A n ^ 2) := by
    intro n
    rw [charFun_walkLaw μ ht n s, hprodG n]
    have hexp_le : ∀ a : ℝ, ‖Complex.exp (-((a : ℂ)) ^ 2 / 2)‖ ≤ 1 := by
      intro a
      have hc : (-((a : ℂ)) ^ 2 / 2) = ((-(a ^ 2) / 2 : ℝ) : ℂ) := by push_cast; ring
      rw [hc, ← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
      nlinarith [sq_nonneg a]
    refine (norm_prod_sub_prod_le _ _ _ (fun i _ ↦ norm_charFun_le_one _)
      (fun i _ ↦ hexp_le _)).trans ?_
    have hterm : ∀ i, ‖charFun μ (walkCoef t k n s i)
        - Complex.exp (-((walkCoef t k n s i : ℂ)) ^ 2 / 2)‖
        ≤ walkCoef t k n s i ^ 2 * (taylorErr μ (A n) + A n ^ 2) := by
      intro i
      set a := walkCoef t k n s i with ha
      have habs : |a| ≤ A n := abs_walkCoef_le n s i
      have h1 : ‖charFun μ a - (1 - (a : ℂ) ^ 2 / 2)‖ ≤ a ^ 2 * taylorErr μ (A n) := by
        refine (norm_charFun_sub_le μ hint hmean hvar a).trans ?_
        exact mul_le_mul_of_nonneg_left
          (taylorErr_mono μ hint (abs_nonneg a) habs) (sq_nonneg a)
      have h2 : ‖(1 - (a : ℂ) ^ 2 / 2) - Complex.exp (-((a : ℂ) ^ 2) / 2)‖ ≤ a ^ 2 * A n ^ 2 := by
        rw [norm_sub_rev]
        refine (norm_exp_sub_one_sub_le a).trans ?_
        have hpow : a ^ 4 = a ^ 2 * a ^ 2 := by ring
        have hsq : a ^ 2 ≤ A n ^ 2 := by
          nlinarith [sq_abs a, abs_nonneg a, hA0 n]
        rw [hpow]
        exact mul_le_mul_of_nonneg_left hsq (sq_nonneg a)
      have h3 : charFun μ a - Complex.exp (-((a : ℂ)) ^ 2 / 2)
          = (charFun μ a - (1 - (a : ℂ) ^ 2 / 2))
            + ((1 - (a : ℂ) ^ 2 / 2) - Complex.exp (-((a : ℂ) ^ 2) / 2)) := by ring
      rw [h3]
      refine (norm_add_le _ _).trans ?_
      have := add_le_add h1 h2
      calc ‖charFun μ a - (1 - (a : ℂ) ^ 2 / 2)‖
            + ‖(1 - (a : ℂ) ^ 2 / 2) - Complex.exp (-((a : ℂ) ^ 2) / 2)‖
          ≤ a ^ 2 * taylorErr μ (A n) + a ^ 2 * A n ^ 2 := this
        _ = a ^ 2 * (taylorErr μ (A n) + A n ^ 2) := by ring
    refine (Finset.sum_le_sum fun i _ ↦ hterm i).trans ?_
    rw [← Finset.sum_mul, hV]
  have hzero : Tendsto (fun n ↦ charFun (walkLaw μ t k n) s - G n) atTop (𝓝 0) := by
    refine squeeze_zero_norm hbound ?_
    have hlim := hVtend.mul ((tendsto_taylorErr μ hint A hA0 hAtend).add
      ((hAtend.pow 2).congr fun n ↦ rfl))
    simpa using hlim
  have hfinal := hzero.add hGtend
  rw [zero_add] at hfinal
  exact hfinal.congr fun n ↦ by ring

end Math2

import Mathlib

/-!
# Lévy's continuity theorem for tight sequences

The main result of this file, `Math2.tendsto_integral_of_tendsto_charFun`, says that a
tight sequence of probability measures on a finite-dimensional inner product space whose
characteristic functions converge pointwise to the characteristic function of a probability
measure `ν` converges weakly to `ν`.

This is the form of Lévy's continuity theorem that is needed for Donsker's invariance principle.
-/

open MeasureTheory ProbabilityTheory Filter Complex
open scoped Topology ENNReal NNReal RealInnerProductSpace BoundedContinuousFunction

namespace Math2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E]

/-- The bounded continuous function `x ↦ exp (i ⟪x, s⟫)`, whose integral against a measure is the
characteristic function of that measure at `s`. -/
noncomputable def charFunBCF (s : E) : E →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x ↦ Complex.exp ((⟪x, s⟫ : ℝ) * Complex.I), by fun_prop⟩ 2 (by
      intro x y
      have hx : ‖Complex.exp (((⟪x, s⟫ : ℝ) : ℂ) * Complex.I)‖ = 1 := by
        simp [Complex.norm_exp_ofReal_mul_I]
      have hy : ‖Complex.exp (((⟪y, s⟫ : ℝ) : ℂ) * Complex.I)‖ = 1 := by
        simp [Complex.norm_exp_ofReal_mul_I]
      simp only [ContinuousMap.coe_mk, dist_eq_norm]
      exact (norm_sub_le _ _).trans (by rw [hx, hy]; norm_num))

omit [BorelSpace E] [FiniteDimensional ℝ E] in
lemma integral_charFunBCF (μ : Measure E) (s : E) :
    ∫ x, charFunBCF s x ∂μ = charFun μ s := by
  rw [charFun_apply]
  rfl

/-- If a sequence of probability measures is tight and its characteristic functions converge
pointwise to those of a probability measure `ν`, then it converges weakly to `ν`. -/
theorem tendsto_probabilityMeasure_of_tendsto_charFun
    (P : ℕ → ProbabilityMeasure E) (Q : ProbabilityMeasure E)
    (htight : IsTightMeasureSet {((P n : Measure E)) | n : ℕ})
    (hchar : ∀ s, Tendsto (fun n ↦ charFun (P n : Measure E) s) atTop
      (𝓝 (charFun (Q : Measure E) s))) :
    Tendsto P atTop (𝓝 Q) := by
  have hcompact : IsCompact (closure (Set.range P)) := by
    refine isCompact_closure_of_isTightMeasureSet ?_
    convert htight using 2
    ext ν
    constructor
    · rintro ⟨R, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨P n, ⟨n, rfl⟩, rfl⟩
  refine tendsto_of_subseq_tendsto fun ns hns ↦ ?_
  have hmem : ∀ n, P (ns n) ∈ closure (Set.range P) := fun n ↦ subset_closure ⟨ns n, rfl⟩
  obtain ⟨Q', -, phi, hphi, hlim⟩ := hcompact.tendsto_subseq hmem
  have hlim' : Tendsto (fun n ↦ P (ns (phi n))) atTop (𝓝 Q') := hlim
  have hQeq : Q' = Q := by
    have hcf : ∀ s : E, charFun (Q' : Measure E) s = charFun (Q : Measure E) s := by
      intro s
      have h1 : Tendsto (fun n ↦ charFun (P (ns (phi n)) : Measure E) s) atTop
          (𝓝 (charFun (Q' : Measure E) s)) := by
        have h := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).1 hlim'
          (charFunBCF s)
        simpa only [integral_charFunBCF] using h
      have h2 : Tendsto (fun n ↦ charFun (P (ns (phi n)) : Measure E) s) atTop
          (𝓝 (charFun (Q : Measure E) s)) := (hchar s).comp (hns.comp hphi.tendsto_atTop)
      exact tendsto_nhds_unique h1 h2
    apply ProbabilityMeasure.toMeasure_injective
    exact Measure.ext_of_charFun (funext hcf)
  exact ⟨phi, hQeq ▸ hlim'⟩

/-- Lévy's continuity theorem (tight version), stated for integrals of bounded continuous
functions. -/
theorem tendsto_integral_of_tendsto_charFun
    (μ : ℕ → Measure E) [∀ n, IsProbabilityMeasure (μ n)]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (htight : IsTightMeasureSet {μ n | n : ℕ})
    (hchar : ∀ s, Tendsto (fun n ↦ charFun (μ n) s) atTop (𝓝 (charFun ν s)))
    (f : E →ᵇ ℝ) :
    Tendsto (fun n ↦ ∫ x, f x ∂(μ n)) atTop (𝓝 (∫ x, f x ∂ν)) := by
  set P : ℕ → ProbabilityMeasure E := fun n ↦ ⟨μ n, inferInstance⟩ with hP
  set Q : ProbabilityMeasure E := ⟨ν, inferInstance⟩ with hQ
  have h := tendsto_probabilityMeasure_of_tendsto_charFun P Q htight hchar
  exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 h f

end Math2

import Mathlib

/-!
# Donsker's invariance principle: basic definitions

We set up the objects appearing in Donsker's theorem:

* `Math2.iidLaw μ`: the law on `ℕ → ℝ` of an i.i.d. sequence with step distribution `μ`;
* `Math2.walkVec t k n ω`: the vector `(S_{⌊n t_0⌋}/√n, …, S_{⌊n t_{k-1}⌋}/√n)` of values of the
  rescaled random walk at the times `t 0, …, t (k-1)`;
* `Math2.bmVec t k z`: the vector `(B_{t_0}, …, B_{t_{k-1}})` of values of a Brownian motion
  built from the i.i.d. standard Gaussian increments `z`;
* `Math2.walkLaw μ t k n` and `Math2.bmLaw t k`: the laws of these two random vectors.
-/

open MeasureTheory ProbabilityTheory Filter Complex
open scoped Topology ENNReal NNReal RealInnerProductSpace

namespace Math2

/-- The number of steps performed by the walk before the rescaled time `t j`. -/
noncomputable def stepCount (t : ℕ → ℝ) (n j : ℕ) : ℕ := ⌊(n : ℝ) * t j⌋₊

/-- The `l`-th increment of the sequence of times `t`, where `t (-1)` is interpreted as `0`. -/
noncomputable def incr (t : ℕ → ℝ) (l : ℕ) : ℝ := if l = 0 then t 0 else t l - t (l - 1)

/-- The law of an i.i.d. sequence of real random variables with common distribution `μ`. -/
noncomputable def iidLaw (μ : Measure ℝ) [IsProbabilityMeasure μ] : Measure (ℕ → ℝ) :=
  Measure.infinitePi fun _ : ℕ ↦ μ

instance (μ : Measure ℝ) [IsProbabilityMeasure μ] : IsProbabilityMeasure (iidLaw μ) := by
  rw [iidLaw]; infer_instance

/-- The vector of values at times `t 0, …, t (k-1)` of the rescaled random walk
`W_n(u) = S_{⌊n u⌋} / √n` associated to the sequence of steps `ω`. -/
noncomputable def walkVec (t : ℕ → ℝ) (k n : ℕ) (ω : ℕ → ℝ) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 fun j ↦ (∑ i ∈ Finset.range (stepCount t n j), ω i) / Real.sqrt n

/-- The vector of values at times `t 0, …, t (k-1)` of a Brownian motion whose increments over
the intervals `[t (l-1), t l]` are `√(t l - t (l-1)) * z l`, for `z` an i.i.d. sequence of
standard Gaussian variables. -/
noncomputable def bmVec (t : ℕ → ℝ) (k : ℕ) (z : ℕ → ℝ) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 fun j ↦ ∑ l ∈ Finset.range ((j : ℕ) + 1), Real.sqrt (incr t l) * z l

lemma measurable_walkVec (t : ℕ → ℝ) (k n : ℕ) : Measurable (walkVec t k n) := by
  unfold walkVec; fun_prop

lemma measurable_bmVec (t : ℕ → ℝ) (k : ℕ) : Measurable (bmVec t k) := by
  unfold bmVec; fun_prop

/-- The law of the rescaled random walk sampled at the times `t 0, …, t (k-1)`, when the steps
are i.i.d. with distribution `μ`. -/
noncomputable def walkLaw (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℕ → ℝ) (k n : ℕ) :
    Measure (EuclideanSpace ℝ (Fin k)) :=
  (iidLaw μ).map (walkVec t k n)

/-- The law of the vector `(B_{t_0}, …, B_{t_{k-1}})` of values of a Brownian motion, i.e. the
finite-dimensional distribution of Brownian motion at the times `t 0, …, t (k-1)`. -/
noncomputable def bmLaw (t : ℕ → ℝ) (k : ℕ) : Measure (EuclideanSpace ℝ (Fin k)) :=
  (iidLaw (gaussianReal 0 1)).map (bmVec t k)

instance (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℕ → ℝ) (k n : ℕ) :
    IsProbabilityMeasure (walkLaw μ t k n) := by
  rw [walkLaw]
  exact Measure.isProbabilityMeasure_map (measurable_walkVec t k n).aemeasurable

instance (t : ℕ → ℝ) (k : ℕ) : IsProbabilityMeasure (bmLaw t k) := by
  rw [bmLaw]
  exact Measure.isProbabilityMeasure_map (measurable_bmVec t k).aemeasurable

/-- The coefficient of `ω i` in the scalar product `⟪walkVec t k n ω, s⟫`. -/
noncomputable def walkCoef (t : ℕ → ℝ) (k n : ℕ) (s : EuclideanSpace ℝ (Fin k)) (i : ℕ) : ℝ :=
  (∑ j : Fin k, if i < stepCount t n j then s j else 0) / Real.sqrt n

/-- The coefficient of `z l` in the scalar product `⟪bmVec t k z, s⟫`. -/
noncomputable def bmCoef (t : ℕ → ℝ) (k : ℕ) (s : EuclideanSpace ℝ (Fin k)) (l : ℕ) : ℝ :=
  Real.sqrt (incr t l) * ∑ j : Fin k, if l ≤ (j : ℕ) then s j else 0

end Math2

import RequestProject.Donsker.Defs

/-!
# Characteristic functions of the rescaled walk and of the Brownian vector

We compute the characteristic functions of `Math2.walkLaw` and `Math2.bmLaw` as products of
one-dimensional characteristic functions, and we identify the characteristic function of
`Math2.bmLaw` with that of a centered Gaussian vector with covariance `min (t i) (t j)`, i.e.
with the finite-dimensional distribution of Brownian motion.
-/

open MeasureTheory ProbabilityTheory Filter Complex
open scoped Topology ENNReal NNReal RealInnerProductSpace

namespace Math2

variable {k : ℕ} {t : ℕ → ℝ}

/-- The characteristic function of a finite linear combination of i.i.d. real random variables
is the product of the characteristic functions of the summands. -/
lemma integral_exp_sum_iid (μ : Measure ℝ) [IsProbabilityMeasure μ] (N : ℕ) (a : ℕ → ℝ) :
    ∫ ω, Complex.exp (((∑ i ∈ Finset.range N, a i * ω i : ℝ) : ℂ) * Complex.I) ∂(iidLaw μ)
      = ∏ i ∈ Finset.range N, charFun μ (a i) := by
  have hindep : iIndepFun (fun (i : Fin N) (ω : ℕ → ℝ) ↦ ω i) (iidLaw μ) := by
    have := iIndepFun_infinitePi (P := fun _ : ℕ ↦ μ) (X := fun _ : ℕ ↦ (id : ℝ → ℝ))
      (fun _ ↦ measurable_id)
    exact this.precomp (g := (Fin.val : Fin N → ℕ)) Fin.val_injective
  have hmap : ∀ i : ℕ, (iidLaw μ).map (fun ω : ℕ → ℝ ↦ ω i) = μ :=
    fun i ↦ Measure.infinitePi_map_eval _ i
  have h1 : ∀ ω : ℕ → ℝ, Complex.exp (((∑ i ∈ Finset.range N, a i * ω i : ℝ) : ℂ) * Complex.I)
      = ∏ i : Fin N, Complex.exp ((ω i : ℂ) * (a i : ℂ) * Complex.I) := by
    intro ω
    rw [← Complex.exp_sum, ← Fin.sum_univ_eq_sum_range (fun i ↦ a i * ω i) N]
    push_cast
    rw [Finset.sum_mul]
    exact congrArg _ (Finset.sum_congr rfl fun i _ ↦ by ring)
  simp_rw [h1]
  rw [hindep.integral_fun_prod_comp
    (f := fun (i : Fin N) (x : ℝ) ↦ Complex.exp ((x : ℂ) * (a i : ℂ) * Complex.I))
    (fun i ↦ (measurable_pi_apply _).aemeasurable)
    (fun i ↦ (by fun_prop :
      Continuous fun x : ℝ ↦ Complex.exp ((x : ℂ) * (a i : ℂ) * Complex.I)).aestronglyMeasurable)]
  rw [← Fin.prod_univ_eq_prod_range (fun i ↦ charFun μ (a i)) N]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [← integral_map (φ := fun ω : ℕ → ℝ ↦ ω (i : ℕ)) (measurable_pi_apply _).aemeasurable
    (by fun_prop : AEStronglyMeasurable
      (fun x : ℝ ↦ Complex.exp ((x : ℂ) * (a i : ℂ) * Complex.I)) _), hmap,
    charFun_apply_real]
  exact congrArg _ (funext fun y ↦ by ring_nf)

/-- The scalar product of the rescaled walk vector with `s`, written as a linear combination of
the steps. -/
lemma inner_walkVec (ht : Monotone t) (n : ℕ) (ω : ℕ → ℝ) (s : EuclideanSpace ℝ (Fin k)) :
    ⟪walkVec t k n ω, s⟫ = ∑ i ∈ Finset.range (stepCount t n k), walkCoef t k n s i * ω i := by
  have hle : ∀ j : Fin k, stepCount t n j ≤ stepCount t n k := by
    intro j
    apply Nat.floor_le_floor
    have : t j ≤ t k := ht (le_of_lt j.isLt)
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hcoord : ∀ j : Fin k, (walkVec t k n ω) j
      = (∑ i ∈ Finset.range (stepCount t n j), ω i) / Real.sqrt n := fun j ↦ rfl
  have key : ∀ j : Fin k, ∑ i ∈ Finset.range (stepCount t n j), ω i
      = ∑ i ∈ Finset.range (stepCount t n k), (if i < stepCount t n j then ω i else 0) := by
    intro j
    rw [← Finset.sum_filter]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h ↦ ⟨lt_of_lt_of_le h (hle j), h⟩, fun h ↦ h.2⟩
  rw [PiLp.inner_apply]
  simp only [hcoord, RCLike.inner_apply, conj_trivial, walkCoef, key,
    mul_div_assoc', Finset.mul_sum, Finset.sum_div, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  split_ifs <;> ring

/-- The scalar product of the Brownian vector with `s`, written as a linear combination of the
increments. -/
lemma inner_bmVec (k : ℕ) (t : ℕ → ℝ) (z : ℕ → ℝ) (s : EuclideanSpace ℝ (Fin k)) :
    ⟪bmVec t k z, s⟫ = ∑ l ∈ Finset.range k, bmCoef t k s l * z l := by
  have hcoord : ∀ j : Fin k, (bmVec t k z) j
      = ∑ l ∈ Finset.range ((j : ℕ) + 1), Real.sqrt (incr t l) * z l := fun j ↦ rfl
  have key : ∀ j : Fin k, ∑ l ∈ Finset.range ((j : ℕ) + 1), Real.sqrt (incr t l) * z l
      = ∑ l ∈ Finset.range k, (if l ≤ (j : ℕ) then Real.sqrt (incr t l) * z l else 0) := by
    intro j
    rw [← Finset.sum_filter]
    congr 1
    ext l
    simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
    exact ⟨fun h ↦ ⟨lt_of_le_of_lt h j.isLt, h⟩, fun h ↦ h.2⟩
  rw [PiLp.inner_apply]
  simp only [hcoord, RCLike.inner_apply, conj_trivial, bmCoef, key,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  split_ifs <;> ring

/-- The characteristic function of the law of the rescaled walk. -/
lemma charFun_walkLaw (μ : Measure ℝ) [IsProbabilityMeasure μ] (ht : Monotone t) (n : ℕ)
    (s : EuclideanSpace ℝ (Fin k)) :
    charFun (walkLaw μ t k n) s
      = ∏ i ∈ Finset.range (stepCount t n k), charFun μ (walkCoef t k n s i) := by
  rw [charFun_apply, walkLaw, integral_map (measurable_walkVec t k n).aemeasurable (by fun_prop),
    ← integral_exp_sum_iid μ (stepCount t n k) (walkCoef t k n s)]
  exact congrArg _ (funext fun ω ↦ by rw [inner_walkVec ht])

/-- The characteristic function of the finite-dimensional distribution of Brownian motion. -/
lemma charFun_bmLaw (k : ℕ) (t : ℕ → ℝ) (s : EuclideanSpace ℝ (Fin k)) :
    charFun (bmLaw t k) s
      = Complex.exp (-(((∑ l ∈ Finset.range k, (bmCoef t k s l) ^ 2 : ℝ) : ℂ)) / 2) := by
  rw [charFun_apply, bmLaw, integral_map (measurable_bmVec t k).aemeasurable (by fun_prop)]
  have h : ∀ z : ℕ → ℝ, Complex.exp ((⟪bmVec t k z, s⟫ : ℝ) * Complex.I)
      = Complex.exp (((∑ l ∈ Finset.range k, bmCoef t k s l * z l : ℝ) : ℂ) * Complex.I) := by
    intro z; rw [inner_bmVec]
  simp_rw [h]
  rw [integral_exp_sum_iid (gaussianReal 0 1) k (bmCoef t k s)]
  simp only [charFun_gaussianReal]
  push_cast
  rw [← Complex.exp_sum]
  congr 1
  rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun l _ ↦ by ring

/-- The increments of `t` sum up to `t`. -/
lemma sum_incr (t : ℕ → ℝ) (m : ℕ) : ∑ l ∈ Finset.range (m + 1), incr t l = t m := by
  induction m with
  | zero => simp [incr]
  | succ m ih =>
      rw [Finset.sum_range_succ, ih, incr]
      simp

lemma incr_nonneg (ht : Monotone t) (ht0 : 0 ≤ t 0) (l : ℕ) : 0 ≤ incr t l := by
  unfold incr
  split_ifs with h
  · exact ht0
  · have hle : l - 1 ≤ l := Nat.sub_le _ _
    linarith [ht hle]

/-- The variance of `⟪bmVec t k z, s⟫` equals the quadratic form with matrix
`min (t i) (t j)`. -/
lemma sum_sq_bmCoef (k : ℕ) (t : ℕ → ℝ) (ht : Monotone t) (ht0 : 0 ≤ t 0)
    (s : EuclideanSpace ℝ (Fin k)) :
    ∑ l ∈ Finset.range k, (bmCoef t k s l) ^ 2
      = ∑ i : Fin k, ∑ j : Fin k, min (t i) (t j) * s i * s j := by
  have hsq : ∀ l, (bmCoef t k s l) ^ 2
      = incr t l * ∑ i : Fin k, ∑ j : Fin k,
          (if l ≤ (i : ℕ) then (1 : ℝ) else 0) * (if l ≤ (j : ℕ) then (1 : ℝ) else 0)
            * (s i * s j) := by
    intro l
    rw [bmCoef, mul_pow, Real.sq_sqrt (incr_nonneg ht ht0 l)]
    congr 1
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    split_ifs <;> ring
  simp only [hsq, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hfac : ∑ l ∈ Finset.range k, incr t l *
      ((if l ≤ (i : ℕ) then (1 : ℝ) else 0) * (if l ≤ (j : ℕ) then (1 : ℝ) else 0) * (s i * s j))
      = (∑ l ∈ Finset.range k, (if l ≤ min (i : ℕ) (j : ℕ) then incr t l else 0))
        * (s i * s j) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    by_cases h1 : l ≤ (i : ℕ) <;> by_cases h2 : l ≤ (j : ℕ) <;>
      simp [h1, h2]
  have hres : ∑ l ∈ Finset.range k, (if l ≤ min (i : ℕ) (j : ℕ) then incr t l else 0)
      = ∑ l ∈ Finset.range (min (i : ℕ) (j : ℕ) + 1), incr t l := by
    rw [← Finset.sum_filter]
    congr 1
    ext l
    simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨lt_of_le_of_lt (h.trans (min_le_left _ _)) i.isLt, h⟩⟩
  rw [hfac, hres, sum_incr]
  have : t (min (i : ℕ) (j : ℕ)) = min (t i) (t j) := by
    rcases le_total (i : ℕ) (j : ℕ) with h | h
    · rw [min_eq_left h, min_eq_left (ht h)]
    · rw [min_eq_right h, min_eq_right (ht h)]
  rw [this, mul_assoc]

/-- `Math2.bmLaw` is the centered Gaussian law with covariance `min (t i) (t j)`: it is indeed
the finite-dimensional distribution of Brownian motion at the times `t 0, …, t (k-1)`. -/
theorem charFun_bmLaw_eq (k : ℕ) (t : ℕ → ℝ) (ht : Monotone t) (ht0 : 0 ≤ t 0)
    (s : EuclideanSpace ℝ (Fin k)) :
    charFun (bmLaw t k) s
      = Complex.exp (-((∑ i : Fin k, ∑ j : Fin k, min (t i) (t j) * s i * s j : ℝ) : ℂ) / 2) := by
  rw [charFun_bmLaw, sum_sq_bmCoef k t ht ht0 s]

end Math2

