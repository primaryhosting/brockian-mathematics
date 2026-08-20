/-
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Statement: The 7-qubit Steane (CSS) code corrects any single-qubit error.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Statement: The 7-qubit Steane (CSS) code corrects any single-qubit error.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

/-! ## Basic setting: 7 qubits, computational basis indexed by bit strings -/

/-- Labels of the computational basis of `(ℂ²)^{⊗7}`: bit strings of length 7. -/
abbrev Bits := Fin 7 → ZMod 2

/-- Syndrome values: three bits (one per parity check of each CSS type). -/
abbrev Chk := Fin 3 → ZMod 2

/-- A state of the 7-qubit register, in the computational basis. -/
abbrev State := Bits → ℂ

/-- Mod-2 inner product of two bit strings. -/

theorem logical_independent (x y : ℂ) (h : x • logicalZero + y • logicalOne = 0) :
    x = 0 ∧ y = 0 := by
  constructor
  · have h0 := congrFun h 0
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, logicalZero, logicalOne,
      if_pos (show RS 0 by decide), if_neg (show ¬ RS ((0 : Bits) + ones) by decide)] at h0
    simpa using h0
  · have h1 := congrFun h ones
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, logicalZero, logicalOne,
      if_neg (show ¬ RS ones by decide), if_pos (show RS (ones + ones) by decide)] at h1
    simpa using h1

/-! ## Arbitrary (not necessarily Pauli) single-qubit errors -/

/-- `X_v` as a linear map. -/
