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

theorem tendsto_walkLaw_measureReal_Iic' {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hmean : ∫ y, y ∂μ = 0) (hvar : ∫ y, y ^ 2 ∂μ = 1)
    (h3 : Integrable (fun y : ℝ => |y| ^ 3) μ) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    Tendsto (fun n : ℕ => (walkLaw μ n t).real (Iic x)) atTop
      (𝓝 ((gaussianReal 0 t.toNNReal).real (Iic x))) := by
  rcases eq_or_lt_of_le ht with rfl | ht'
  · have hzero : ∀ n : ℕ, walkLaw μ n 0 = gaussianReal 0 (0 : ℝ).toNNReal := by
      intro n
      have hc : ((n : ℝ) * 0) = 0 := by ring
      rw [walkLaw, hc]
      simp [scaledLaw, Measure.map_dirac (measurable_const_mul ((Real.sqrt n)⁻¹))]
    simp only [hzero]
    exact tendsto_const_nhds
  · have hne : t.toNNReal ≠ 0 := by simpa using ht'
    exact tendsto_scaledLaw_measureReal_Iic hmean hvar h3
      (m := fun n => ⌊(n : ℝ) * t⌋₊) (tendsto_floor_div t ht) x (Or.inl hne)

