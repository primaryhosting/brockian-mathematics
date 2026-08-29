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

theorem exists_bound_sTrans3 : ∃ C : ℝ, 0 ≤ C ∧ ∀ y, |sTrans3 y| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f := sTrans3) (s := Icc (0 : ℝ) 1) sTrans3_contDiff.continuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun y => ?_⟩
  rcases lt_trichotomy y 0 with hy | hy | hy
  · rw [sTrans3_eq_zero_of_lt_zero y hy]
    simp
  · have : y ∈ Icc (0 : ℝ) 1 := by simp [hy]
    exact le_trans (by simpa [Real.norm_eq_abs] using hC y this) (le_max_left _ _)
  · rcases le_or_gt y 1 with hy1 | hy1
    · have : y ∈ Icc (0 : ℝ) 1 := ⟨hy.le, hy1⟩
      exact le_trans (by simpa [Real.norm_eq_abs] using hC y this) (le_max_left _ _)
    · rw [sTrans3_eq_zero_of_one_lt y hy1]
      simp

/-- A smooth function which is `1` on `Iic x`, `0` on `Ici (x + δ)` and takes values in
`[0,1]`, together with its first three derivatives and a common bound. -/
