import Mathlib

/-!
# Deutsch Correct
Category: Quantum Computing
Target: QC.deutsch_correct
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

namespace QC

/-! ## The two-qubit state space

A two-qubit state is described by its amplitude function `Bool × Bool → ℂ`,
where `(x, y)` denotes the computational basis state `|x⟩ ⊗ |y⟩`
(with `false = 0` and `true = 1`). -/

/-- The sign `(-1)^b`. -/

lemma norm_invSqrt2_sq : ‖invSqrt2‖ ^ 2 = (1 : ℝ) / 2 := by
  have h : ‖invSqrt2‖ = (Real.sqrt 2)⁻¹ := by
    simp [invSqrt2, Complex.norm_real, abs_of_nonneg (by positivity : (0:ℝ) ≤ (Real.sqrt 2)⁻¹)]
  rw [h]
  rw [inv_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

/-- Explicit form of the final state. -/
