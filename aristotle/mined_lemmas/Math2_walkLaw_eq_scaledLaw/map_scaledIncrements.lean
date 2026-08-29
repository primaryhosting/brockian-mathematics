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

theorem map_scaledIncrements (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, P.map (X i) = μ) {a : ℕ → ℕ} (ha : Monotone a) (n k : ℕ) :
    P.map (fun ω (j : Fin k) =>
        (∑ i ∈ Finset.Ico (a j) (a (j + 1)), X i ω) / Real.sqrt n)
      = Measure.pi (fun j : Fin k => scaledLaw μ (a (j + 1) - a j) n) := by
  have hblocks := map_blockSums_eq_pi hmeas hindep hident ha k
  have hmeasv : Measurable
      (fun (ω : Ω) (j : Fin k) => ∑ i ∈ Finset.Ico (a j) (a (j + 1)), X i ω) :=
    measurable_pi_lambda _ fun j => measurable_blockSum hmeas _ _
  have hscale : Measurable (fun (v : Fin k → ℝ) (j : Fin k) => (Real.sqrt n)⁻¹ * v j) := by
    fun_prop
  have hcomp : (fun (ω : Ω) (j : Fin k) =>
        (∑ i ∈ Finset.Ico (a j) (a (j + 1)), X i ω) / Real.sqrt n)
      = (fun (v : Fin k → ℝ) (j : Fin k) => (Real.sqrt n)⁻¹ * v j)
        ∘ (fun (ω : Ω) (j : Fin k) => ∑ i ∈ Finset.Ico (a j) (a (j + 1)), X i ω) := by
    funext ω j
    simp [Function.comp, div_eq_inv_mul]
  rw [hcomp, ← Measure.map_map hscale hmeasv, hblocks,
    Measure.pi_map_pi (fun j => (measurable_const_mul (Real.sqrt n)⁻¹).aemeasurable)]
  rfl

omit [MeasurableSpace Ω] in
/-- The vector of rescaled positions is the vector of partial sums of the rescaled increments. -/
