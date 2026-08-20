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
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

/-! ## Classical setup: the Hamming `[7,4,3]` code and its dual -/

/-- Bit strings of length 7 (the computational basis labels of 7 qubits). -/
abbrev Bits := Fin 7 → ZMod 2

/-- The parity check matrix of the classical Hamming `[7,4,3]` code. -/

theorem wtv_add_le (u v : Bits) : wtv (u + v) ≤ wtv u + wtv v := by
  classical
  have hsub : (Finset.univ.filter (fun i => (u + v) i ≠ 0)) ⊆
      (Finset.univ.filter (fun i => u i ≠ 0)) ∪ (Finset.univ.filter (fun i => v i ≠ 0)) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Pi.add_apply] at hi ⊢
    by_contra hcon
    push_neg at hcon
    simp [hcon.1, hcon.2] at hi
  calc wtv (u + v) ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _

/-! ## Character sums over the dual code -/

