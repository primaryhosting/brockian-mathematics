import Mathlib
/-!
# Gleason Theorem
Category: Frontier Physics
Target: Frontier.gleason_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical
open scoped ComplexOrder

set_option maxHeartbeats 1000000

namespace Frontier

open Matrix

variable {n : ℕ}

/-! ## Basic notions -/

/-- The rank-one (orthogonal) projection onto the line spanned by a unit vector `v`,
written as the matrix `v vᴴ`. -/

theorem isQuantumMeasure_qubitMeasure : IsQuantumMeasure qubitMeasure := by
  refine ⟨fun P _ => qubitMeasure_nonneg P, fun P Q hP hQ hPQ => ?_, qubitMeasure_one⟩
  by_cases hP0 : P = 0
  · rw [hP0, zero_add, qubitMeasure_zero, zero_add]
  by_cases hQ0 : Q = 0
  · rw [hQ0, add_zero, qubitMeasure_zero, add_zero]
  have hsum : P + Q = 1 := proj2_add_eq_one hP hQ hPQ hP0 hQ0
  have hQeq : Q = 1 - P := by rw [← hsum]; abel
  rw [hsum, hQeq, qubitMeasure_one]
  exact (qubitMeasure_add_compl hP).symm

/-! ## `qubitMeasure` does not come from a density operator -/

/-- Unit vectors used to defeat any candidate density operator. -/
