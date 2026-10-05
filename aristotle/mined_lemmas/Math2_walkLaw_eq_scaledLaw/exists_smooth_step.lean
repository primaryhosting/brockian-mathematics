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

theorem exists_smooth_step (x δ : ℝ) (hδ : 0 < δ) :
    ∃ (f f1 f2 f3 : ℝ → ℝ) (M : ℝ), IsC3Test f f1 f2 f3 M ∧
      (∀ y, 0 ≤ f y) ∧ (∀ y, f y ≤ 1) ∧ (∀ y ≤ x, f y = 1) ∧
      (∀ y, x + δ ≤ y → f y = 0) := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_sTrans3
  set r : ℝ := -δ⁻¹ with hr
  set u : ℝ → ℝ := fun y => (x + δ - y) / δ with hu
  have hu' : ∀ y, HasDerivAt u r y := by
    intro y
    have : HasDerivAt (fun y : ℝ => (x + δ - y) / δ) ((0 - 1) / δ) y := by
      exact (((hasDerivAt_id y).const_sub (x + δ)).div_const δ).congr_deriv (by ring)
    simpa [hr, hu, div_eq_mul_inv] using this
  refine ⟨fun y => sTrans0 (u y), fun y => sTrans1 (u y) * r, fun y => sTrans2 (u y) * r ^ 2,
    fun y => sTrans3 (u y) * r ^ 3, max 1 (C * |r| ^ 3), ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro y
    exact (hasDerivAt_sTrans0 (u y)).comp y (hu' y)
  · intro y
    have := ((hasDerivAt_sTrans1 (u y)).comp y (hu' y)).mul_const r
    convert this using 1
    ring
  · intro y
    have := ((hasDerivAt_sTrans2 (u y)).comp y (hu' y)).mul_const (r ^ 2)
    convert this using 1
    ring
  · intro y
    have h0 : |sTrans0 (u y)| ≤ 1 := by
      show |Real.smoothTransition (u y)| ≤ 1
      rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
      exact Real.smoothTransition.le_one _
    exact h0.trans (le_max_left _ _)
  · intro y
    have : |sTrans3 (u y) * r ^ 3| ≤ C * |r| ^ 3 := by
      rw [abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_right (hC _) (by positivity)
    exact this.trans (le_max_right _ _)
  · intro y
    exact Real.smoothTransition.nonneg _
  · intro y
    exact Real.smoothTransition.le_one _
  · intro y hy
    have : 1 ≤ u y := by
      rw [hu]
      rw [le_div_iff₀ hδ]
      linarith
    exact Real.smoothTransition.one_of_one_le this
  · intro y hy
    have : u y ≤ 0 := by
      rw [hu, div_nonpos_iff]
      right
      constructor <;> linarith
    exact Real.smoothTransition.zero_of_nonpos this

end Math2

import RequestProject.Walk

/-!
# Joint law of the increments of a random walk

For an i.i.d. sequence `X` with law `μ` and an increasing sequence of times `a 0 ≤ a 1 ≤ ⋯`, the
block sums `∑_{a j ≤ i < a (j+1)} X i` are independent, the `j`-th one having law
`convPow μ (a (j+1) - a j)`.  We record this as an identity between the joint law of the vector of
block sums and the product of the convolution powers.
-/

namespace Math2

open MeasureTheory ProbabilityTheory Filter Set

section Blocks

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]

/-- The law of a single block sum `X p + ⋯ + X (q-1)` is the convolution power of order `q - p`. -/
