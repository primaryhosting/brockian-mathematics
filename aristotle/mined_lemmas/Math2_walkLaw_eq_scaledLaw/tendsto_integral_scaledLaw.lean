import RequestProject.CLT

/-!
# Convergence of the rescaled walk against smooth test functions

`Math2.walkLaw μ n t` is the law of `S_{⌊n t⌋} / √n`, where `S` is a random walk with step
distribution `μ`.  Here we prove that, for a centered step distribution with unit variance and
finite third absolute moment, the integrals of smooth test functions against `walkLaw μ n t`
converge to the corresponding integrals against the centered Gaussian law of variance `t`, which
is the law of Brownian motion at time `t`.
-/

namespace Math2

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

/-- The law of `S_p / √n`, the sum of `p` i.i.d. steps with law `μ`, rescaled by `1/√n`. -/

theorem tendsto_integral_scaledLaw {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hmean : ∫ x, x ∂μ = 0) (hvar : ∫ x, x ^ 2 ∂μ = 1)
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ)
    {f f1 f2 f3 : ℝ → ℝ} {M : ℝ} (h : IsC3Test f f1 f2 f3 M) {m : ℕ → ℕ} {v : ℝ}
    (hm : Tendsto (fun n : ℕ => (m n : ℝ) / n) atTop (𝓝 v)) :
    Tendsto (fun n : ℕ => ∫ x, f x ∂(scaledLaw μ (m n) n)) atTop
      (𝓝 (∫ x, f x ∂(gaussianReal 0 v.toNNReal))) := by
  have hvnn : 0 ≤ v := by
    refine ge_of_tendsto hm ?_
    filter_upwards with n using by positivity
  set K : ℝ := M * ((∫ x, |x| ^ 3 ∂μ) + gaussThirdMoment) with hK
  have hKnn : 0 ≤ K := by
    have h1 : 0 ≤ ∫ x, |x| ^ 3 ∂μ := integral_nonneg fun x => by positivity
    have h2 : 0 ≤ gaussThirdMoment := integral_nonneg fun x => by positivity
    have := h.nonneg
    rw [hK]; positivity
  set w : ℕ → ℝ≥0 := fun n =>
    (m n : ℕ) • (⟨((Real.sqrt n)⁻¹) ^ 2, sq_nonneg _⟩ : ℝ≥0) with hw
  -- Step 1 : the Lindeberg estimate tends to zero
  have hdiff : Tendsto
      (fun n : ℕ => (∫ x, f x ∂(scaledLaw μ (m n) n)) - ∫ x, f x ∂(gaussianReal 0 (w n)))
      atTop (𝓝 0) := by
    have hsqrt : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    have hzero : Tendsto (fun n : ℕ => (m n : ℝ) / n * K / Real.sqrt n) atTop (𝓝 0) :=
      Tendsto.div_atTop (hm.mul_const K) hsqrt
    refine squeeze_zero_norm' ?_ hzero
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
    have hbound := walk_gaussian_bound hmean hvar h3 h (Real.sqrt n)⁻¹ (m n)
    rw [← scaledLaw] at hbound
    have habs : |((Real.sqrt n)⁻¹)| ^ 3 = 1 / ((n : ℝ) * Real.sqrt n) := by
      rw [abs_of_pos (inv_pos.2 hsn), inv_pow, one_div]
      congr 1
      have h3' : Real.sqrt n ^ 3 = Real.sqrt n ^ 2 * Real.sqrt n := by ring
      rw [h3', Real.sq_sqrt hn0.le]
    have heq : (m n : ℝ) * (K * (1 / ((n : ℝ) * Real.sqrt n)))
        = (m n : ℝ) / n * K / Real.sqrt n := by
      field_simp
    calc ‖(∫ x, f x ∂(scaledLaw μ (m n) n)) - ∫ x, f x ∂(gaussianReal 0 (w n))‖
        = |(∫ x, f x ∂(scaledLaw μ (m n) n)) - ∫ x, f x ∂(gaussianReal 0 (w n))| := by
          rw [Real.norm_eq_abs]
      _ ≤ (m n : ℝ) * (M * (|((Real.sqrt n)⁻¹)| ^ 3
            * ((∫ x, |x| ^ 3 ∂μ) + gaussThirdMoment))) := hbound
      _ = (m n : ℝ) * (K * (1 / ((n : ℝ) * Real.sqrt n))) := by
          rw [habs, hK]; ring
      _ = (m n : ℝ) / n * K / Real.sqrt n := heq
  -- Step 2 : the Gaussian laws converge
  have hwlim : Tendsto w atTop (𝓝 v.toNNReal) := by
    rw [← NNReal.tendsto_coe]
    have hcoe : ∀ n : ℕ, 0 < n → ((w n : ℝ≥0) : ℝ) = (m n : ℝ) / n := by
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have h1 : ((w n : ℝ≥0) : ℝ) = (m n : ℝ) * ((Real.sqrt n)⁻¹) ^ 2 := by
        rw [hw]
        push_cast [nsmul_eq_mul]
        rfl
      rw [h1, inv_pow, Real.sq_sqrt hn0.le]
      field_simp
    rw [Real.coe_toNNReal v hvnn]
    refine hm.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [hcoe n hn]
  have hgauss : Tendsto (fun n : ℕ => ∫ x, f x ∂(gaussianReal 0 (w n))) atTop
      (𝓝 (∫ x, f x ∂(gaussianReal 0 v.toNNReal))) :=
    tendsto_integral_gaussianReal_of_tendsto h.continuous h.bound0 hwlim
  have := hdiff.add hgauss
  simpa using this

/-- The convergence statement for smooth test functions at a fixed time `t ≥ 0`: the rescaled
walk at time `t` converges to the centered Gaussian of variance `t`. -/
