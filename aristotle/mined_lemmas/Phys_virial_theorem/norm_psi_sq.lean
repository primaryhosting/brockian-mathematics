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

lemma norm_psi_sq (x : ℝ) : ‖psi x‖ ^ 2 = Real.exp (-x ^ 2) := by
  rw [psi, Complex.norm_real, Real.norm_eq_abs, sq_abs, sq, exp_half_sq]

