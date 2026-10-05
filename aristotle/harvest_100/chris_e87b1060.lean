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
def pauliI : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 1]

/-- The Pauli matrix `X`. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli matrix `Y`. -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- The Pauli matrix `Z`. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The family `![I, X, Y, Z]` of Pauli matrices, indexed by `Fin 4`. -/
def paulis : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ := ![pauliI, pauliX, pauliY, pauliZ]

theorem finrank_matrix_two : Module.finrank ℂ (Matrix (Fin 2) (Fin 2) ℂ) = 4 := by
  rw [Module.finrank_matrix]
  simp

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
theorem pauli_basis :
    ∃ b : Module.Basis (Fin 4) ℂ (Matrix (Fin 2) (Fin 2) ℂ), ⇑b = paulis := by
  refine ⟨basisOfLinearIndependentOfCardEqFinrank paulis_linearIndependent ?_, ?_⟩
  · simp [finrank_matrix_two]
  · exact coe_basisOfLinearIndependentOfCardEqFinrank _ _

/-- The Pauli matrices span the space of `2 × 2` complex matrices. -/
theorem paulis_span : Submodule.span ℂ (Set.range paulis) = ⊤ := by
  obtain ⟨b, hb⟩ := pauli_basis
  rw [← hb, ← Module.Basis.span_eq b]

end QC

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

