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

theorem exists_delta_cdf_gaussianReal (v : ℝ≥0) (x : ℝ) (hx : v ≠ 0 ∨ x ≠ 0) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ > 0, (gaussianReal 0 v).real (Iic (x + δ)) ≤ (gaussianReal 0 v).real (Iic x) + ε ∧
      (gaussianReal 0 v).real (Iic x) - ε ≤ (gaussianReal 0 v).real (Iic (x - δ)) := by
  rcases eq_or_ne v 0 with rfl | hv
  · have hx0 : x ≠ 0 := hx.resolve_left (by simp)
    have hdir : ∀ y : ℝ,
        (Measure.dirac (0 : ℝ)).real (Iic y) = if (0 : ℝ) ≤ y then 1 else 0 := by
      intro y
      rw [Measure.real, Measure.dirac_apply' _ measurableSet_Iic]
      by_cases hy : (0 : ℝ) ≤ y
      · rw [Set.indicator_of_mem (Set.mem_Iic.2 hy)]; simp [hy]
      · rw [Set.indicator_of_notMem (by simpa using hy)]; simp [hy]
    simp only [gaussianReal_zero_var, hdir]
    refine ⟨|x| / 2, by positivity, ?_, ?_⟩
    · rcases lt_or_gt_of_ne hx0 with hneg | hpos
      · rw [abs_of_neg hneg]; split_ifs <;> linarith
      · rw [abs_of_pos hpos]; split_ifs <;> linarith
    · rcases lt_or_gt_of_ne hx0 with hneg | hpos
      · rw [abs_of_neg hneg]; split_ifs <;> linarith
      · rw [abs_of_pos hpos]; split_ifs <;> linarith
  · have : NoAtoms (gaussianReal 0 v) := noAtoms_gaussianReal hv
    exact exists_delta_cdf _ x hε

/-- **Convergence of the distribution functions.**  If the number of steps satisfies
`m n / n → v`, the distribution function of `S_{m n} / √n` converges to that of the centered
Gaussian of variance `v` at every point `x` of continuity of the latter. -/
