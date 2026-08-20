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

theorem sum_ind_pair (d : Bits) (f : Bits → ℂ) :
    ∑ c : Bits, (if inC2 c then (1 : ℂ) else 0) * f c * (if inC2 (c + d) then (1 : ℂ) else 0)
      = if inC2 d then ∑ c ∈ Finset.univ.filter inC2, f c else 0 := by
  by_cases hd : inC2 d
  · simp only [hd, if_true]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc : inC2 c
    · have hcd : inC2 (c + d) := (inC2_add_iff hc).2 hd
      simp [hc, hcd]
    · simp [hc]
  · simp only [hd, if_false]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hc : inC2 c
    · have hcd : ¬ inC2 (c + d) := by rw [inC2_add_iff hc]; exact hd
      simp [hcd]
    · simp [hc]

/-- The general matrix element of a product of two Pauli operators between logical
basis states. -/
