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

lemma norm_dpsi_sq (x : ℝ) : ‖dpsi x‖ ^ 2 = x ^ 2 * Real.exp (-x ^ 2) := by
  rw [dpsi, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [mul_pow, sq (Real.exp _), exp_half_sq]
  ring

