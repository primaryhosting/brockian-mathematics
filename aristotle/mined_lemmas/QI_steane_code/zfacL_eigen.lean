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

lemma zfacL_eigen (s t : ZMod 2) (k : Fin 3) (phi : State)
    (h : Zop (Hrow k) phi = sgn t • phi) :
    zfacL s k phi = (if s = t then (1 : ℂ) else 0) • phi := by
  have hZ : ZopL (Hrow k) phi = sgn t • phi := h
  simp only [zfacL, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply, hZ, smul_smul]
  by_cases hst : s = t
  · subst hst
    rw [sgn_mul_self, if_pos rfl, one_smul, ← two_smul ℂ phi, smul_smul]
    norm_num
  · rw [sgn_mul_of_ne hst, if_neg hst, zero_smul, neg_one_smul, add_neg_cancel, smul_zero]

