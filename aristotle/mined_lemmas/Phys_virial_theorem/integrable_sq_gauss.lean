/-
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Filter MeasureTheory Topology Complex

namespace Phys

/-- `‖z‖ ^ 2` in terms of the real and imaginary parts of `z`. -/

private lemma integrable_sq_gauss : Integrable fun x : ℝ => x ^ 2 * Real.exp (-x ^ 2) := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => x ^ 2 * Real.exp (-x ^ 2)) volume := by
    fun_prop
  have hg : Integrable fun x : ℝ => 2 * Real.exp (-(1 / 2) * x ^ 2) :=
    (integrable_exp_neg_mul_sq (b := 1 / 2) (by norm_num)).const_mul 2
  refine Integrable.mono' hg hmeas (Filter.Eventually.of_forall fun x => ?_)
  have hx : x ^ 2 / 2 ≤ Real.exp (x ^ 2 / 2) := (Real.add_one_le_exp _).trans' (by linarith)
  have hpos : (0:ℝ) < Real.exp (-x ^ 2) := Real.exp_pos _
  have hsplit : Real.exp (-x ^ 2) = Real.exp (-(1 / 2) * x ^ 2) * Real.exp (-(x ^ 2 / 2)) := by
    rw [← Real.exp_add]; ring_nf
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hsplit]
  have hinv : Real.exp (-(x ^ 2 / 2)) * Real.exp (x ^ 2 / 2) = 1 := by
    rw [← Real.exp_add]; simp
  have h2 : x ^ 2 * Real.exp (-(x ^ 2 / 2)) ≤ 2 := by
    nlinarith [Real.exp_pos (-(x ^ 2 / 2)), Real.exp_pos (x ^ 2 / 2)]
  calc x ^ 2 * (Real.exp (-(1 / 2) * x ^ 2) * Real.exp (-(x ^ 2 / 2)))
      = (x ^ 2 * Real.exp (-(x ^ 2 / 2))) * Real.exp (-(1 / 2) * x ^ 2) := by ring
    _ ≤ 2 * Real.exp (-(1 / 2) * x ^ 2) := by
        exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le

