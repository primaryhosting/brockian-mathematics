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

theorem charsum_eq_zero {b : Bits} (h : ∃ c : Bits, inC2 c ∧ dotp b c = 1) :
    charsum b = 0 := by
  obtain ⟨c0, hc0, hdot⟩ := h
  have hmem : ∀ c : Bits, c ∈ Finset.univ.filter inC2 ↔
      (Equiv.addRight c0) c ∈ Finset.univ.filter inC2 := by
    intro c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_addRight]
    constructor
    · intro hc; exact inC2_add hc hc0
    · intro hc
      have : inC2 (c0 + (c + c0)) := inC2_add hc0 hc
      have e : c0 + (c + c0) = c := by
        have : c0 + (c + c0) = c + (c0 + c0) := by abel
        rw [this, add_self_bits, add_zero]
      rwa [e] at this
  have key : ∑ c ∈ Finset.univ.filter inC2, sgn (dotp b (c + c0)) = charsum b := by
    unfold charsum
    exact Finset.sum_equiv (Equiv.addRight c0) hmem (fun c _ => rfl)
  have key2 : ∑ c ∈ Finset.univ.filter inC2, sgn (dotp b (c + c0)) = -charsum b := by
    unfold charsum
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [dotp_add_right, sgn_add, hdot]
    simp [sgn]
  rw [key] at key2
  linear_combination key2 / 2

/-! ## The core computation -/

