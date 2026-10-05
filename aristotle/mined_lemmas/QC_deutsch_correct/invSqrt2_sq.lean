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

lemma invSqrt2_sq : invSqrt2 * invSqrt2 = (2 : ℂ)⁻¹ := by
  have h : (Real.sqrt 2) * (Real.sqrt 2) = 2 := Real.mul_self_sqrt (by norm_num)
  have : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, h]; norm_num
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    intro hc
    rw [hc] at this
    norm_num at this
  simp only [invSqrt2, Complex.ofReal_inv]
  field_simp [this]

