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
def PI : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 1]

/-- The Pauli matrix `X`. -/
def PX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli matrix `Y`. -/
def PY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- The Pauli matrix `Z`. -/
def PZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The family of the four Pauli matrices, indexed by `Fin 4`. -/
def paulis : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ := ![PI, PX, PY, PZ]

/-- The four Pauli matrices are linearly independent over `ℂ`. -/
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
noncomputable def pauliBasis : Module.Basis (Fin 4) ℂ (Matrix (Fin 2) (Fin 2) ℂ) :=
  basisOfLinearIndependentOfCardEqFinrank paulis_linearIndependent (by
    simp [Module.finrank_matrix])

@[simp] lemma pauliBasis_apply : ⇑pauliBasis = paulis :=
  coe_basisOfLinearIndependentOfCardEqFinrank _ _

/-- **Pauli basis**: `{I, X, Y, Z}` is a basis of the `ℂ`-vector space of `2 × 2`
complex matrices, i.e. the family is linearly independent and spans the whole space. -/
theorem pauli_basis :
    LinearIndependent ℂ paulis ∧ Submodule.span ℂ (Set.range paulis) = ⊤ := by
  refine ⟨paulis_linearIndependent, ?_⟩
  have h := pauliBasis.span_eq
  rwa [pauliBasis_apply] at h

end QC

#print axioms QC.pauli_basis

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

