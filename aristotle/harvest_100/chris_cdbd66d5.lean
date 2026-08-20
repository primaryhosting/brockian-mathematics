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

/-- The Pauli matrix `X`. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli matrix `Y`. -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- The Pauli matrix `Z`. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The family `{I, X, Y, Z}` of Pauli matrices, indexed by `Fin 4`. -/
def pauli : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ := ![1, pauliX, pauliY, pauliZ]

/-- The Pauli matrices are linearly independent over `ℂ`. -/
theorem pauli_linearIndependent : LinearIndependent ℂ pauli := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  rw [Fin.sum_univ_four] at hg
  have h00 := congrFun (congrFun hg 0) 0
  have h01 := congrFun (congrFun hg 0) 1
  have h10 := congrFun (congrFun hg 1) 0
  have h11 := congrFun (congrFun hg 1) 1
  simp [pauli, pauliX, pauliY, pauliZ] at h00 h01 h10 h11
  have hI : (Complex.I) ≠ 0 := Complex.I_ne_zero
  have hg0 : g 0 = 0 := by
    have : g 0 + g 3 = 0 := h00
    have h2 : g 0 - g 3 = 0 := by linear_combination h11
    linear_combination (this + h2) / 2
  have hg3 : g 3 = 0 := by
    have : g 0 + g 3 = 0 := h00
    linear_combination this - hg0
  have hg1 : g 1 = 0 := by
    have hs : (g 1 - Complex.I * g 2) + (g 1 + Complex.I * g 2) = 0 := by
      linear_combination h01 + h10
    linear_combination hs / 2
  have hg2 : g 2 = 0 := by
    have hd : Complex.I * g 2 = 0 := by linear_combination h10 - hg1
    exact (mul_eq_zero.mp hd).resolve_left hI
  fin_cases i <;> assumption

/-- The Pauli matrices span the space of `2 × 2` complex matrices. -/
theorem pauli_span : Submodule.span ℂ (Set.range pauli) = ⊤ := by
  refine pauli_linearIndependent.span_eq_top_of_card_eq_finrank ?_
  rw [Module.finrank_matrix]
  simp

/-- **Pauli basis**: `{I, X, Y, Z}` is a basis of the `ℂ`-vector space of `2 × 2`
complex matrices. -/
theorem pauli_basis :
    ∃ B : Module.Basis (Fin 4) ℂ (Matrix (Fin 2) (Fin 2) ℂ), ⇑B = pauli :=
  ⟨Module.Basis.mk pauli_linearIndependent pauli_span.ge, by ext i; simp⟩

/-- The basis of `2 × 2` complex matrices given by the Pauli matrices. -/
noncomputable def pauliBasis : Module.Basis (Fin 4) ℂ (Matrix (Fin 2) (Fin 2) ℂ) :=
  Module.Basis.mk pauli_linearIndependent pauli_span.ge

@[simp] theorem coe_pauliBasis : ⇑pauliBasis = pauli := by
  ext i; simp [pauliBasis]

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

