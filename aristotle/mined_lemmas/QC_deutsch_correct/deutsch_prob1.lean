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

A state of two qubits is a function `Bool × Bool → ℂ` assigning an amplitude to each
computational basis state `|x y⟩`. -/

/-- The sign `(-1)^b`. -/

theorem deutsch_prob1 (f : Bool → Bool) :
    prob1 f = if f false = f true then 0 else 1 := by
  have hnorm : ‖rt2‖ = Real.sqrt 2 := by
    simp [rt2, Real.sqrt_nonneg]
  simp only [prob1, deutschState_true, sgn]
  cases f false <;> cases f true <;>
    simp [hnorm, div_pow] <;>
    · field_simp
      rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      norm_num

/-- Sanity check: the final state is normalized, i.e. the two measurement outcomes for the
first qubit have probabilities summing to `1`. -/
