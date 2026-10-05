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

theorem measureReal_Iic_le_integral (h : IsC3Test f f1 f2 f3 M) (hf0 : ∀ y, 0 ≤ f y)
    (hf1 : ∀ y ≤ x, f y = 1) : ν.real (Iic x) ≤ ∫ y, f y ∂ν := by
  have hind : Integrable ((Iic x).indicator (fun _ => (1 : ℝ))) ν :=
    (integrable_indicator_iff measurableSet_Iic).2 (by simp)
  have hle : ∀ y, (Iic x).indicator (fun _ => (1 : ℝ)) y ≤ f y := by
    intro y
    by_cases hy : y ≤ x
    · rw [Set.indicator_of_mem (Set.mem_Iic.2 hy), hf1 y hy]
    · rw [Set.indicator_of_notMem (by simpa using hy)]
      exact hf0 y
  have := integral_mono hind (h.integrable ν) hle
  rwa [show ((Iic x).indicator (fun _ => (1 : ℝ))) = (Iic x).indicator 1 from rfl,
    integral_indicator_one measurableSet_Iic] at this

/-- The integral of a test function bounded by `1` and vanishing on `Ici x` is at most the
measure of `Iic x`. -/
