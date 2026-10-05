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

theorem tendsto_scaledLaw_measureReal_Iic {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hmean : ∫ y, y ∂μ = 0) (hvar : ∫ y, y ^ 2 ∂μ = 1)
    (h3 : Integrable (fun y : ℝ => |y| ^ 3) μ) {m : ℕ → ℕ} {v : ℝ}
    (hm : Tendsto (fun n : ℕ => (m n : ℝ) / n) atTop (𝓝 v)) (x : ℝ)
    (hx : v.toNNReal ≠ 0 ∨ x ≠ 0) :
    Tendsto (fun n : ℕ => (scaledLaw μ (m n) n).real (Iic x)) atTop
      (𝓝 ((gaussianReal 0 v.toNNReal).real (Iic x))) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hup, hlow⟩ :=
    exists_delta_cdf_gaussianReal v.toNNReal x hx (ε := ε / 3) (by linarith)
  obtain ⟨f, f1, f2, f3, M, hf, hf0, hf1, hfone, hfzero⟩ := exists_smooth_step x δ hδ
  obtain ⟨g, g1, g2, g3, N, hg, hg0, hg1, hgone, hgzero⟩ := exists_smooth_step (x - δ) δ hδ
  have hfconv := tendsto_integral_scaledLaw hmean hvar h3 hf hm
  have hgconv := tendsto_integral_scaledLaw hmean hvar h3 hg hm
  rw [Metric.tendsto_atTop] at hfconv hgconv
  obtain ⟨N₁, hN₁⟩ := hfconv (ε / 3) (by linarith)
  obtain ⟨N₂, hN₂⟩ := hgconv (ε / 3) (by linarith)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have hn₁ : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn₂ : N₂ ≤ n := le_trans (le_max_right _ _) hn
  have hfn := hN₁ n hn₁
  have hgn := hN₂ n hn₂
  rw [Real.dist_eq] at hfn hgn ⊢
  have hupper : (scaledLaw μ (m n) n).real (Iic x) ≤
      (gaussianReal 0 v.toNNReal).real (Iic x) + 2 * (ε / 3) := by
    have h1 : (scaledLaw μ (m n) n).real (Iic x) ≤ ∫ y, f y ∂(scaledLaw μ (m n) n) :=
      measureReal_Iic_le_integral hf hf0 (fun y hy => hfone y hy)
    have h2 : (∫ y, f y ∂(gaussianReal 0 v.toNNReal))
        ≤ (gaussianReal 0 v.toNNReal).real (Iic (x + δ)) :=
      integral_le_measureReal_Iic hf hf1 (fun y hy => hfzero y hy)
    have h3' : (∫ y, f y ∂(scaledLaw μ (m n) n))
        ≤ (∫ y, f y ∂(gaussianReal 0 v.toNNReal)) + ε / 3 := by
      have := abs_lt.1 hfn
      linarith [this.2]
    linarith
  have hlower : (gaussianReal 0 v.toNNReal).real (Iic x) - 2 * (ε / 3) ≤
      (scaledLaw μ (m n) n).real (Iic x) := by
    have h1 : (∫ y, g y ∂(scaledLaw μ (m n) n)) ≤ (scaledLaw μ (m n) n).real (Iic x) := by
      refine integral_le_measureReal_Iic hg hg1 (fun y hy => hgzero y ?_)
      linarith
    have h2 : (gaussianReal 0 v.toNNReal).real (Iic (x - δ))
        ≤ ∫ y, g y ∂(gaussianReal 0 v.toNNReal) :=
      measureReal_Iic_le_integral hg hg0 (fun y hy => hgone y hy)
    have h3' : (∫ y, g y ∂(gaussianReal 0 v.toNNReal)) - ε / 3
        ≤ ∫ y, g y ∂(scaledLaw μ (m n) n) := by
      have := abs_lt.1 hgn
      linarith [this.1]
    linarith
  rw [abs_lt]
  constructor <;> linarith

/-- **Convergence of the distribution functions of the rescaled walk**, for every time `t ≥ 0`. -/
