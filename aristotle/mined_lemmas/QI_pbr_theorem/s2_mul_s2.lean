/-
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

/-! ### Two-qubit vectors, inner products and the states involved -/

/-- A (pure) qubit state vector. -/
abbrev Qubit := Fin 2 → ℂ

/-- A two-qubit state vector, written in curried form. -/
abbrev TwoQubit := Fin 2 → Fin 2 → ℂ

/-- The product (tensor) of two qubit vectors. -/

lemma s2_mul_s2 : (s2 : ℂ) * (s2 : ℂ) = 1 / 2 := by
  have h : s2 * s2 = 1 / 2 := by
    rw [s2, ← mul_inv, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  rw [← Complex.ofReal_mul, h]
  norm_num

/-- The computational basis state `|0⟩`. -/
