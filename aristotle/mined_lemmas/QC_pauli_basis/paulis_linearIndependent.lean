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

theorem paulis_linearIndependent : LinearIndependent ℂ paulis := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  rw [Fin.sum_univ_four] at hg
  simp only [paulis, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three,
    pauliI, pauliX, pauliY, pauliZ] at hg
  have h00 := congrFun (congrFun hg 0) 0
  have h01 := congrFun (congrFun hg 0) 1
  have h10 := congrFun (congrFun hg 1) 0
  have h11 := congrFun (congrFun hg 1) 1
  simp [Matrix.add_apply] at h00 h01 h10 h11
  -- `h00 : g 0 + g 3 = 0`, `h11 : g 0 - g 3 = 0`,
  -- `h01 : g 1 - g 2 * I = 0`, `h10 : g 1 + g 2 * I = 0`
  have hh : g 2 * Complex.I = 0 := by linear_combination (h10 - h01) / 2
  have h2 : g 2 = 0 := by simpa [Complex.I_ne_zero] using hh
  have h1 : g 1 = 0 := by linear_combination h10 - hh
  have h0 : g 0 = 0 := by linear_combination (h00 + h11) / 2
  have h3 : g 3 = 0 := by linear_combination (h00 - h11) / 2
  fin_cases i <;> assumption

/-- The Pauli matrices `{I, X, Y, Z}` form a basis of the `ℂ`-vector space of `2 × 2`
complex matrices. -/
