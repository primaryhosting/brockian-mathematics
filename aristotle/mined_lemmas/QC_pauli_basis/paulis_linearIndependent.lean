/-
# Pauli Basis
Category: Quantum Computing
Target: QC.pauli_basis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

lemma paulis_linearIndependent : LinearIndependent ℂ paulis := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h00 := congrFun (congrFun hg 0) 0
  have h01 := congrFun (congrFun hg 0) 1
  have h10 := congrFun (congrFun hg 1) 0
  have h11 := congrFun (congrFun hg 1) 1
  clear hg
  simp only [paulis, PI, PX, PY, PZ, Fin.sum_univ_four, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.zero_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.cons_val, smul_eq_mul, mul_one, mul_zero,
    Matrix.of_apply] at h00 h01 h10 h11
  have e0 : g 0 = 0 := by linear_combination h00 / 2 + h11 / 2
  have e1 : g 1 = 0 := by linear_combination h01 / 2 + h10 / 2
  have e2 : g 2 = 0 := by
    linear_combination (Complex.I / 2) * h01 - (Complex.I / 2) * h10 + g 2 * Complex.I_sq
  have e3 : g 3 = 0 := by linear_combination h00 / 2 - h11 / 2
  fin_cases i <;> assumption

/-- The four Pauli matrices, as a basis of the `ℂ`-vector space of `2 × 2` complex
matrices. -/
