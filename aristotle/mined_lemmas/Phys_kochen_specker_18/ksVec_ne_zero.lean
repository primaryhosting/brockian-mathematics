import Mathlib

/-!
# Kochen Specker 18
Category: Frontier Phys
Target: Phys.kochen_specker_18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Phys

/-- The 18 vectors of the Cabello–Estebaranz–García-Alcaine Kochen–Specker set in `ℝ⁴`. -/

theorem ksVec_ne_zero (i : Fin 18) : ksVec i ≠ 0 := by
  intro h
  have h3 := congrFun h 3
  have h2 := congrFun h 2
  have h1 := congrFun h 1
  have h0 := congrFun h 0
  fin_cases i <;> simp [ksVec] at h0 h1 h2 h3

/-- Within each of the nine listed quadruples, the four vectors are pairwise orthogonal;
hence each quadruple really is an orthogonal basis of `ℝ⁴`. -/
