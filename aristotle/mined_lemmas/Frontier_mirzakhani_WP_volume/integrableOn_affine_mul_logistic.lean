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

lemma integrableOn_affine_mul_logistic (a b c d : ℝ) :
    IntegrableOn (fun x => (b * x + c) * logistic (x + d)) (Ioi a) volume := by
  apply integrable_of_isBigO_exp_neg (b := 1/4) (by norm_num)
  · exact (((continuous_const.mul continuous_id).add continuous_const).mul
      (continuous_logistic.comp (continuous_id.add continuous_const))).continuousOn
  · rw [isBigO_iff]
    refine ⟨Real.exp (-d/2) * (4 * |b| + |c|), ?_⟩
    filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with y hy
    have hp : (0:ℝ) < Real.exp (-y/4) := Real.exp_pos _
    have hd : (0:ℝ) < Real.exp (-d/2) := Real.exp_pos _
    have e4 : Real.exp (-y/4) * Real.exp (y/4) = 1 := by rw [← Real.exp_add]; ring_nf; simp
    have hy4 : y * Real.exp (-y/4) ≤ 4 := by
      have h := Real.add_one_le_exp (y/4); nlinarith
    have hle1 : Real.exp (-y/4) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have hsplit : Real.exp (-(y+d)/2) = Real.exp (-d/2) * (Real.exp (-y/4) * Real.exp (-y/4)) := by
      rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    have hbound : ‖(b * y + c) * logistic (y + d)‖ ≤ (|b| * y + |c|) * Real.exp (-(y+d)/2) := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (logistic_pos _)]
      have hab : |b * y + c| ≤ |b| * y + |c| := by
        calc |b * y + c| ≤ |b * y| + |c| := abs_add_le _ _
        _ = |b| * y + |c| := by rw [abs_mul, abs_of_nonneg hy]
      have hL := logistic_le_exp (y + d)
      have hLpos := logistic_pos (y + d)
      have h0 : (0:ℝ) ≤ |b| * y + |c| := by positivity
      nlinarith [Real.exp_pos (-(y+d)/2), abs_nonneg (b * y + c)]
    have hnorm : ‖Real.exp (-(1/4:ℝ) * y)‖ = Real.exp (-y/4) := by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]; ring_nf
    rw [hnorm]
    calc ‖(b * y + c) * logistic (y + d)‖ ≤ (|b| * y + |c|) * Real.exp (-(y+d)/2) := hbound
      _ = Real.exp (-d/2) * ((|b| * (y * Real.exp (-y/4))) * Real.exp (-y/4)
            + |c| * (Real.exp (-y/4) * Real.exp (-y/4))) := by rw [hsplit]; ring
      _ ≤ Real.exp (-d/2) * ((|b| * 4) * Real.exp (-y/4) + |c| * Real.exp (-y/4)) := by
          have h1 : (|b| * (y * Real.exp (-y/4))) * Real.exp (-y/4)
              ≤ (|b| * 4) * Real.exp (-y/4) := by
            have hb : |b| * (y * Real.exp (-y/4)) ≤ |b| * 4 :=
              mul_le_mul_of_nonneg_left hy4 (abs_nonneg b)
            exact mul_le_mul_of_nonneg_right hb hp.le
          have h2 : |c| * (Real.exp (-y/4) * Real.exp (-y/4)) ≤ |c| * Real.exp (-y/4) := by
            have hee : Real.exp (-y/4) * Real.exp (-y/4) ≤ Real.exp (-y/4) := by nlinarith
            exact mul_le_mul_of_nonneg_left hee (abs_nonneg c)
          nlinarith
      _ = Real.exp (-d/2) * (4 * |b| + |c|) * Real.exp (-y/4) := by ring

/-- Integrability of `y ↦ (b y + c) · logistic y` on any half-line. -/
