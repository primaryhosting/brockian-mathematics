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

lemma integral_Ioc_reflect {t : ℝ} (ht : 0 ≤ t) :
    ∫ y in Ioc (-t) t, (y + t) * logistic y
      = t ^ 2 / 2 + ∫ y in Ioc (0:ℝ) t, 2 * y * logistic y := by
  have hcont : Continuous (fun y : ℝ => (y + t) * logistic y) :=
    (continuous_id.add continuous_const).mul continuous_logistic
  have hcont2 : Continuous (fun y : ℝ => 2 * y * logistic y) :=
    (continuous_const.mul continuous_id).mul continuous_logistic
  have hcont3 : Continuous (fun x : ℝ => (t - x) * (1 - logistic x)) :=
    (continuous_const.sub continuous_id).mul (continuous_const.sub continuous_logistic)
  have hcont4 : Continuous (fun x : ℝ => t - x) := continuous_const.sub continuous_id
  rw [← intervalIntegral.integral_of_le (by linarith : (-t:ℝ) ≤ t),
      ← intervalIntegral.integral_of_le ht]
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (a := -t) (b := 0) (c := t) (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have hcn := intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := t)
      (fun y => (y + t) * logistic y)
  simp only [neg_zero] at hcn
  have hneg : ∫ y in (-t)..0, (y + t) * logistic y
      = ∫ x in (0:ℝ)..t, (t - x) * (1 - logistic x) := by
    rw [← hcn]
    apply intervalIntegral.integral_congr
    intro x _
    have h2 : logistic (-x) = 1 - logistic x := by have := logistic_add_neg x; linarith
    simp only [h2]
    ring
  rw [hneg, ← intervalIntegral.integral_add (hcont3.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)]
  have hpoint : ∫ x in (0:ℝ)..t, ((t - x) * (1 - logistic x) + (x + t) * logistic x)
      = ∫ x in (0:ℝ)..t, ((t - x) + 2 * x * logistic x) := by
    apply intervalIntegral.integral_congr
    intro x _
    simp only
    ring
  rw [hpoint, intervalIntegral.integral_add (hcont4.intervalIntegrable _ _)
      (hcont2.intervalIntegrable _ _)]
  congr 1
  rw [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id]
  simp [integral_id]
  ring

/-- The basic kernel integral for nonnegative `t`. -/
