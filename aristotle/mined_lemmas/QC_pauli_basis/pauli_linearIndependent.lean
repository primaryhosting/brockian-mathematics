import Mathlib

/-!
# Pauli Basis
Category: Quantum Computing
Target: QC.pauli_basis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Matrix

/-- The identity Pauli matrix `I`. -/

lemma pauli_linearIndependent : LinearIndependent ℂ pauli := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h00 := congrFun (congrFun hg 0) 0
  have h01 := congrFun (congrFun hg 0) 1
  have h10 := congrFun (congrFun hg 1) 0
  have h11 := congrFun (congrFun hg 1) 1
  simp [Fin.sum_univ_four, pauli, pauliI, pauliX, pauliY, pauliZ] at h00 h01 h10 h11
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hg0 : g 0 = 0 := by linear_combination (h00 + h11) / 2
  have hg3 : g 3 = 0 := by linear_combination (h00 - h11) / 2
  have hg1 : g 1 = 0 := by linear_combination (h01 + h10) / 2
  have hg2 : g 2 = 0 := by
    have h : Complex.I * g 2 = 0 := by linear_combination (h10 - h01) / 2
    exact (mul_eq_zero.mp h).resolve_left hI
  intro i
  fin_cases i <;> assumption

