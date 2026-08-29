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

private lemma tendsto_abs_gauss_atBot :
    Tendsto (fun x : ℝ => |x| * Real.exp (-x ^ 2)) atBot (𝓝 0) := by
  have h := tendsto_abs_gauss_cocompact
  rw [cocompact_eq_atBot_atTop] at h
  exact h.mono_left le_sup_left

