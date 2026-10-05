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

private lemma exp_half_sq (x : ℝ) :
    Real.exp (-x ^ 2 / 2) * Real.exp (-x ^ 2 / 2) = Real.exp (-x ^ 2) := by
  rw [← Real.exp_add]; ring_nf

