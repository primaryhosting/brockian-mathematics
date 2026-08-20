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

theorem ip_pauli_pauli (a b a' b' : Bits) (i j : ZMod 2) :
    ip (pauli a b (psi i)) (pauli a' b' (psi j))
      = if inC2 (a + a' + (lvec i + lvec j)) then
          sgn (dotp b (lvec i)) * sgn (dotp b' (lvec i + (a + a'))) * charsum (b + b')
        else 0 := by
  have expand : ip (pauli a b (psi i)) (pauli a' b' (psi j))
      = ∑ c : Bits, (if inC2 c then (1 : ℂ) else 0) *
          (sgn (dotp (b + b') c) * (sgn (dotp b (lvec i)) * sgn (dotp b' (lvec i + (a + a'))))) *
          (if inC2 (c + (a + a' + (lvec i + lvec j))) then (1 : ℂ) else 0) := by
    unfold ip
    rw [shift_sum (lvec i + a)]
    refine Finset.sum_congr rfl fun c _ => ?_
    have e2 : c + (lvec i + a) + a = c + lvec i := by
      have h : c + (lvec i + a) + a = c + lvec i + (a + a) := by abel
      rw [h, add_self_bits, add_zero]
    have e4 : c + (lvec i + a) + a' = c + (lvec i + (a + a')) := by abel
    have e1 : c + lvec i + lvec i = c := bits_cancel c (lvec i)
    have e3 : c + (lvec i + (a + a')) + lvec j = c + (a + a' + (lvec i + lvec j)) := by abel
    simp only [pauli, psi, e2, e4, e1, e3, map_mul, sgn_conj, ind_conj]
    rw [dotp_add_right, dotp_add_right, sgn_add, sgn_add, dotp_add_left, sgn_add]
    ring
  rw [expand, sum_ind_pair]
  by_cases hd : inC2 (a + a' + (lvec i + lvec j))
  · simp only [hd, if_true]
    rw [← Finset.sum_mul, ← charsum]
    ring
  · simp [hd]

/-! ## Main theorem -/

/-- **The Steane code corrects any single-qubit error.**

`psi 0, psi 1` span the code space of the 7-qubit Steane CSS code, and `pauli a b`
with `wt a b ≤ 1` ranges over the Pauli operators supported on at most one qubit;
these span all operators acting on a single qubit.  The identity below is exactly the
Knill–Laflamme error-correction condition
`⟨ψᵢ| E† F |ψⱼ⟩ = c_{E,F} δᵢⱼ`
for that error set, with the nondegenerate coefficient matrix `c_{E,F} = 8 δ_{E,F}`
(8 being the squared norm of the unnormalised logical states). -/
