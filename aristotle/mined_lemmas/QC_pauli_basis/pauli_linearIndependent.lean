import Mathlib

/-!
# Pauli Basis
Category: Quantum Computing
Target: QC.pauli_basis
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

/-- The 2×2 identity (Pauli `I`). -/

lemma pauli_linearIndependent : LinearIndependent ℂ pauli := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  rw [pauli_comb] at hc
  have h00 : c 0 + c 3 = 0 := by
    have := congrFun (congrFun hc 0) 0; simpa using this
  have h11 : c 0 - c 3 = 0 := by
    have := congrFun (congrFun hc 1) 1; simpa using this
  have h01 : c 1 - Complex.I * c 2 = 0 := by
    have := congrFun (congrFun hc 0) 1; simpa using this
  have h10 : c 1 + Complex.I * c 2 = 0 := by
    have := congrFun (congrFun hc 1) 0; simpa using this
  have hc0 : c 0 = 0 := by linear_combination (h00 + h11) / 2
  have hc3 : c 3 = 0 := by linear_combination (h00 - h11) / 2
  have hc1 : c 1 = 0 := by linear_combination (h01 + h10) / 2
  have hc2 : c 2 = 0 := by
    have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
    have : Complex.I * c 2 = 0 := by linear_combination (h10 - h01) / 2
    exact (mul_eq_zero.1 this).resolve_left hI
  fin_cases i <;> assumption

