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

theorem exists_delta_cdf (γ : Measure ℝ) [IsProbabilityMeasure γ] [NoAtoms γ] (x : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, γ.real (Iic (x + δ)) ≤ γ.real (Iic x) + ε ∧
      γ.real (Iic x) - ε ≤ γ.real (Iic (x - δ)) := by
  obtain ⟨δ, hδ, hwin⟩ := exists_small_window γ x hε
  have hd1 : γ.real (Iic (x + δ)) = γ.real (Iic x) + γ.real (Ioc x (x + δ)) := by
    rw [← measureReal_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc,
      Set.Iic_union_Ioc_eq_Iic (by linarith)]
  have hd2 : γ.real (Iic x) = γ.real (Iic (x - δ)) + γ.real (Ioc (x - δ) x) := by
    rw [← measureReal_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc,
      Set.Iic_union_Ioc_eq_Iic (by linarith)]
  have hsub1 : γ.real (Ioc x (x + δ)) ≤ γ.real (Ioc (x - δ) (x + δ)) :=
    measureReal_mono (Ioc_subset_Ioc (by linarith) le_rfl)
  have hsub2 : γ.real (Ioc (x - δ) x) ≤ γ.real (Ioc (x - δ) (x + δ)) :=
    measureReal_mono (Ioc_subset_Ioc le_rfl (by linarith))
  exact ⟨δ, hδ, by linarith, by linarith⟩

end CDF

section Sandwich

variable {f f1 f2 f3 : ℝ → ℝ} {M x : ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]

/-- The measure of `Iic x` is at most the integral of a nonnegative test function which is `1`
on `Iic x`. -/
