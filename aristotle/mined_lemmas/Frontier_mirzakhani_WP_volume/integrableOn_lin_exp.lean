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

lemma integrableOn_lin_exp {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun y => y * Real.exp (-(r*y))) (Ioi 0) volume := by
  apply integrable_of_isBigO_exp_neg (b := r/2) (by linarith)
  · fun_prop
  · rw [isBigO_iff]
    refine ⟨2/r, ?_⟩
    filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with y hy
    have hp : (0:ℝ) < Real.exp (-(r/2*y)) := Real.exp_pos _
    have e4 : Real.exp (-(r/2*y)) * Real.exp (r/2*y) = 1 := by
      rw [← Real.exp_add]; ring_nf; simp
    have hy4 : y * Real.exp (-(r/2*y)) ≤ 2/r := by
      have h := Real.add_one_le_exp (r/2*y)
      have h2 : y * r ≤ 2 * Real.exp (r/2*y) := by nlinarith
      rw [le_div_iff₀ hr]
      nlinarith [mul_le_mul_of_nonneg_right h2 hp.le]
    have hsplit : Real.exp (-(r*y)) = Real.exp (-(r/2*y)) * Real.exp (-(r/2*y)) := by
      rw [← Real.exp_add]; ring_nf
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ y * Real.exp (-(r*y)))]
    have hre : Real.exp (-(r/2) * y) = Real.exp (-(r/2*y)) := by ring_nf
    rw [hre]
    calc y * Real.exp (-(r*y)) = (y * Real.exp (-(r/2*y))) * Real.exp (-(r/2*y)) := by
          rw [hsplit]; ring
      _ ≤ (2/r) * Real.exp (-(r/2*y)) := mul_le_mul_of_nonneg_right hy4 hp.le

/-! ## Translation of half-line integrals -/

