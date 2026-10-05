/-
# Mirzakhani WP Volume
Category: Frontier — Fields Medal Work
Target: Frontier.mirzakhani_WP_volume
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Mirzakhani WP Volume
Category: Frontier — Fields Medal Work
Target: Frontier.mirzakhani_WP_volume
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

open MeasureTheory Set Real Asymptotics

namespace Frontier

/-! ## Mirzakhani's integration kernel -/

/-- The basic "logistic" profile appearing in Mirzakhani's kernels:
`logistic u = 1 / (1 + exp (u / 2))`. -/

lemma integral_lin_mul_logistic : ∫ y in Ioi (0:ℝ), y * logistic y = π ^ 2 / 3 := by
  set F : ℕ → ℝ → ℝ := fun n y => (-1)^n * (y * Real.exp (-(((n:ℝ)+1)/2 * y))) with hF
  have hr : ∀ n : ℕ, (0:ℝ) < ((n:ℝ)+1)/2 := by intro n; positivity
  have hInt : ∀ n : ℕ, IntegrableOn (F n) (Ioi 0) volume := fun n =>
    (integrableOn_lin_exp (hr n)).const_mul _
  have hvalF : ∀ n : ℕ, ∫ y in Ioi (0:ℝ), F n y = (-1)^n * (4/((n:ℝ)+1)^2) := by
    intro n
    rw [hF]; simp only
    rw [MeasureTheory.integral_const_mul, integral_lin_exp (hr n)]
    congr 1; field_simp; norm_num
  have hnormF : ∀ n : ℕ, ∫ y in Ioi (0:ℝ), ‖F n y‖ = 4/((n:ℝ)+1)^2 := by
    intro n
    have hcong : ∀ y ∈ Ioi (0:ℝ), ‖F n y‖ = y * Real.exp (-(((n:ℝ)+1)/2 * y)) := by
      intro y hy
      simp only [hF, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
        Real.norm_eq_abs, abs_of_pos (mem_Ioi.1 hy), abs_of_pos (Real.exp_pos _)]
    rw [setIntegral_congr_fun measurableSet_Ioi hcong, integral_lin_exp (hr n)]
    field_simp; norm_num
  have hsummable : Summable (fun n : ℕ => ∫ y in Ioi (0:ℝ), ‖F n y‖) := by
    apply ((hasSum_inv_sq_succ.summable).mul_left (4:ℝ)).congr
    intro n; rw [hnormF n]; field_simp
  have key := MeasureTheory.integral_tsum_of_summable_integral_norm hInt hsummable
  have hptw : ∀ y ∈ Ioi (0:ℝ), ∑' n : ℕ, F n y = y * logistic y :=
    fun y hy => (hasSum_logistic_series (mem_Ioi.1 hy)).tsum_eq
  rw [← setIntegral_congr_fun measurableSet_Ioi hptw, ← key]
  have hcv : ∀ n : ℕ, ∫ y in Ioi (0:ℝ), F n y = 4 * ((-1)^n / ((n:ℝ)+1)^2) := by
    intro n; rw [hvalF n]; ring
  rw [tsum_congr hcv, (hasSum_alternating_inv_sq.mul_left 4).tsum_eq]
  ring

/-! ## Mirzakhani's kernel integral -/

/-- The reflection step: `∫_{-t}^{t} (y+t) logistic y dy = t²/2 + ∫_0^t 2y logistic y dy`. -/
