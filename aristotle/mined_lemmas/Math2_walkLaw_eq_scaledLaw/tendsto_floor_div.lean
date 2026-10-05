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

theorem tendsto_floor_div (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ => (⌊(n : ℝ) * t⌋₊ : ℝ) / n) atTop (𝓝 t) := by
  have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have hl : Tendsto (fun n : ℕ => t - 1 / n) atTop (𝓝 t) := by
    have := (tendsto_const_nhds (x := t) (f := atTop (α := ℕ))).sub h0
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have h2 : (n : ℝ) * t - 1 < (⌊(n : ℝ) * t⌋₊ : ℝ) := by
      have := Nat.lt_floor_add_one ((n : ℝ) * t); linarith
    rw [le_div_iff₀ hn0]
    have hinv : (1 / (n : ℝ)) * n = 1 := by field_simp
    nlinarith
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 : (⌊(n : ℝ) * t⌋₊ : ℝ) ≤ (n : ℝ) * t := Nat.floor_le (by positivity)
    rw [div_le_iff₀ hn0]
    linarith

/-- The main convergence statement for smooth test functions: if the number of steps `m n`
satisfies `m n / n → v`, then the law of `S_{m n} / √n` converges to the centered Gaussian of
variance `v`. -/
