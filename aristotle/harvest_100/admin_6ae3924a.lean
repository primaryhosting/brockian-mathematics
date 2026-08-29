/-
# Pauli Basis
Category: Quantum Computing
Target: QC.pauli_basis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

/-- The family `{I, X, Y, Z}` of Pauli matrices, indexed by `Fin 4`. -/
def pauliFamily : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ := ![pauliI, pauliX, pauliY, pauliZ]

/-- The Pauli matrices are linearly independent over `ℂ`. -/
theorem pauli_linearIndependent : LinearIndependent ℂ pauliFamily := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [pauliFamily, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three,
    pauliI, pauliX, pauliY, pauliZ] at hg
  have h00 := congrFun (congrFun hg 0) 0
  have h01 := congrFun (congrFun hg 0) 1
  have h10 := congrFun (congrFun hg 1) 0
  have h11 := congrFun (congrFun hg 1) 1
  simp [Matrix.add_apply, Matrix.zero_apply] at h00 h01 h10 h11
  have hI : (Complex.I) ≠ 0 := Complex.I_ne_zero
  have hsum : g 0 + g 3 = 0 := by linear_combination h00
  have hdif : g 0 - g 3 = 0 := by linear_combination h11
  have hs : g 1 + Complex.I * g 2 = 0 := by linear_combination h10
  have hd : g 1 - Complex.I * g 2 = 0 := by linear_combination h01
  have hg0 : g 0 = 0 := by linear_combination (hsum + hdif) / 2
  have hg3 : g 3 = 0 := by linear_combination (hsum - hdif) / 2
  have hg1 : g 1 = 0 := by linear_combination (hs + hd) / 2
  have hg2 : g 2 = 0 := by
    have h : Complex.I * g 2 = 0 := by linear_combination (hs - hd) / 2
    exact (mul_eq_zero.mp h).resolve_left hI
  intro i
  fin_cases i <;> simpa using ‹_›

/-- The Pauli matrices span the space of `2 × 2` complex matrices. -/
theorem pauli_span : Submodule.span ℂ (Set.range pauliFamily) = ⊤ := by
  have hcard : Fintype.card (Fin 4) = Module.finrank ℂ (Matrix (Fin 2) (Fin 2) ℂ) := by
    simp [Module.finrank_matrix]
  exact pauli_linearIndependent.span_eq_top_of_card_eq_finrank hcard

/-- **The Pauli matrices `{I, X, Y, Z}` form a basis of the ℂ-vector space of `2 × 2`
complex matrices.** -/
theorem pauli_basis :
    ∃ b : Module.Basis (Fin 4) ℂ (Matrix (Fin 2) (Fin 2) ℂ),
      ⇑b = ![pauliI, pauliX, pauliY, pauliZ] :=
  ⟨Module.Basis.mk pauli_linearIndependent pauli_span.ge, by
    ext i; simp [Module.Basis.mk_apply, pauliFamily]⟩

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

