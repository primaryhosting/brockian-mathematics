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

private lemma integrable_gauss : Integrable fun x : ℝ => Real.exp (-x ^ 2) := by
  simpa using integrable_exp_neg_mul_sq (b := 1) one_pos

