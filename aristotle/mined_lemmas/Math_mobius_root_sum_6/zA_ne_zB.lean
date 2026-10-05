/-
# Mobius Root Sum 6
Category: Pure Mathematics
Target: Math.mobius_root_sum_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset Complex

namespace Math

/-- The two primitive 6-th roots of unity, written explicitly. -/
private noncomputable def zA : ℂ := (1 + Complex.I * (Real.sqrt 3 : ℝ)) / 2
private noncomputable def zB : ℂ := (1 - Complex.I * (Real.sqrt 3 : ℝ)) / 2


private lemma zA_ne_zB : zA ≠ zB := by
  have hs : Real.sqrt 3 ≠ 0 := by positivity
  intro hEq
  unfold zA zB at hEq
  have : (Complex.I * (Real.sqrt 3 : ℝ)) = 0 := by linear_combination hEq
  rcases mul_eq_zero.1 this with h | h
  · exact Complex.I_ne_zero h
  · exact hs (by exact_mod_cast h)

