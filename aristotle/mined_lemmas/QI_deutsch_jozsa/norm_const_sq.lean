import Mathlib

/-!
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

variable {n : ℕ}

/-- The computational basis of `n` qubits, indexed by bit strings `Fin n → Bool`. -/
abbrev Bits (n : ℕ) := Fin n → Bool

/-- The all-zeros bit string. -/

theorem norm_const_sq :
    (((Real.sqrt 2 ^ n : ℝ) : ℂ)⁻¹) * (((Real.sqrt 2 ^ n : ℝ) : ℂ)⁻¹) = ((2 : ℂ) ^ n)⁻¹ := by
  have h2 : (Real.sqrt 2) * (Real.sqrt 2) = 2 := Real.mul_self_sqrt (by norm_num)
  have hsq : ((Real.sqrt 2 ^ n : ℝ) : ℂ) * ((Real.sqrt 2 ^ n : ℝ) : ℂ) = (2 : ℂ) ^ n := by
    rw [← Complex.ofReal_mul, ← mul_pow, h2]
    norm_cast
  rw [← mul_inv, hsq]

/-- After the first Hadamard transform the state is uniform. -/
