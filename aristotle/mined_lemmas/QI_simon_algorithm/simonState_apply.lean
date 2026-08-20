/-
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Statement: Simon's problem is solved with O(n) quantum queries but needs Ω(2^{n/2}) classically.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib
import RequestProject.Simon.Defs
import RequestProject.Simon.Quantum
import RequestProject.Simon.Classical
import RequestProject.Simon.Sampling
import RequestProject.Simon.Upper

/-!
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Statement: Simon's problem is solved with O(n) quantum queries but needs Ω(2^{n/2}) classically.
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

namespace QI

open Finset

/-- The measurement outcomes of Simon's circuit form a probability distribution. -/

lemma simonState_apply {n : ℕ} (f : BV n → BV n) (y v : BV n) :
    simonState f y v = (((((2 : ℝ) ^ n)⁻¹ * ramp f y v : ℝ)) : ℂ) := by
  classical
  rw [simonState]
  show ((Real.sqrt (2 ^ n) : ℝ) : ℂ)⁻¹ *
      ∑ x : BV n, sgn (dot x y) * oracleApply f (hadamardFirst (initState n)) x v = _
  simp only [oracle_hadamard_initState]
  simp only [mul_comm (sgn (dot _ y))]
  simp only [mul_assoc]
  rw [← Finset.mul_sum, ← mul_assoc, sqrt_two_pow_inv_sq]
  push_cast [ramp, sgn]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : f x = v <;> simp [hx]

