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

theorem donsker_invariance (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, P.map (X i) = μ) (hmean : ∫ y, y ∂μ = 0) (hvar : ∫ y, y ^ 2 ∂μ = 1)
    (h3 : Integrable (fun y : ℝ => |y| ^ 3) μ) {t : ℝ} (ht : 0 ≤ t) :
    (∀ x : ℝ,
        Tendsto
          (fun n : ℕ => P.real {ω | (∑ i ∈ Finset.range ⌊(n : ℝ) * t⌋₊, X i ω) / Real.sqrt n ≤ x})
          atTop (𝓝 ((gaussianReal 0 t.toNNReal).real (Iic x)))) ∧
      ∀ f : ℝ →ᵇ ℝ,
        Tendsto
          (fun n : ℕ => ∫ ω, f ((∑ i ∈ Finset.range ⌊(n : ℝ) * t⌋₊, X i ω) / Real.sqrt n) ∂P)
          atTop (𝓝 (∫ x, f x ∂(gaussianReal 0 t.toNNReal))) := by
  have hmap : ∀ n : ℕ, P.map (rescaledWalk X n t) = walkLaw μ n t :=
    fun n => map_rescaledWalk hmeas hindep hident n t
  have hmeasw : ∀ n : ℕ, Measurable (rescaledWalk X n t) := by
    intro n
    have hsum : Measurable fun ω => ∑ i ∈ Finset.range ⌊(n : ℝ) * t⌋₊, X i ω :=
      Finset.measurable_sum _ fun i _ => hmeas i
    exact hsum.div_const _
  constructor
  · intro x
    have hset : ∀ n : ℕ,
        P.real {ω | (∑ i ∈ Finset.range ⌊(n : ℝ) * t⌋₊, X i ω) / Real.sqrt n ≤ x}
          = (walkLaw μ n t).real (Iic x) := by
      intro n
      have h1 : P {ω | (∑ i ∈ Finset.range ⌊(n : ℝ) * t⌋₊, X i ω) / Real.sqrt n ≤ x}
          = (walkLaw μ n t) (Iic x) := by
        rw [← hmap n, Measure.map_apply (hmeasw n) measurableSet_Iic]
        rfl
      simp [Measure.real, h1]
    simp only [hset]
    exact tendsto_walkLaw_measureReal_Iic' hmean hvar h3 ht x
  · intro f
    have hint : ∀ n : ℕ,
        ∫ ω, f ((∑ i ∈ Finset.range ⌊(n : ℝ) * t⌋₊, X i ω) / Real.sqrt n) ∂P
          = ∫ y, f y ∂(walkLaw μ n t) := by
      intro n
      rw [← hmap n, integral_map (hmeasw n).aemeasurable f.continuous.aestronglyMeasurable]
      rfl
    simp only [hint]
    exact tendsto_integral_walkLaw_boundedContinuous hmean hvar h3 ht f

end Donsker

end Math2

