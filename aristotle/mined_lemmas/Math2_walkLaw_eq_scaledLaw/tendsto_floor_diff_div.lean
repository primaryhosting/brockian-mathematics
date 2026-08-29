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

theorem tendsto_floor_diff_div {s u : ℝ} (hs : 0 ≤ s) (hsu : s ≤ u) :
    Tendsto (fun n : ℕ => ((⌊(n : ℝ) * u⌋₊ - ⌊(n : ℝ) * s⌋₊ : ℕ) : ℝ) / n) atTop (𝓝 (u - s)) := by
  have hu : 0 ≤ u := le_trans hs hsu
  have hlim := (tendsto_floor_div u hu).sub (tendsto_floor_div s hs)
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hmono : ⌊(n : ℝ) * s⌋₊ ≤ ⌊(n : ℝ) * u⌋₊ := by
    refine Nat.floor_le_floor ?_
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  rw [Nat.cast_sub hmono]
  ring

section Walk

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]

/-- The joint law of the rescaled increments of the walk is the product of the scaled convolution
powers. -/
