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

/-- The family `{I, X, Y, Z}` of Pauli matrices, indexed by `Fin 4`. -/
def pauli : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ := ![pauliI, pauliX, pauliY, pauliZ]

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

lemma pauli_span : Submodule.span ℂ (Set.range pauli) = ⊤ := by
  rw [eq_top_iff]
  rintro M -
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨![(M 0 0 + M 1 1) / 2, (M 0 1 + M 1 0) / 2,
      Complex.I * (M 0 1 - M 1 0) / 2, (M 0 0 - M 1 1) / 2], ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_four, pauli, pauliI, pauliX, pauliY, pauliZ] <;>
    ring_nf <;>
    simp [Complex.I_sq] <;>
    ring

/-- **The Pauli matrices form a basis of the ℂ-vector space of 2×2 complex matrices.**
The family `{I, X, Y, Z}` is linearly independent and spans `Matrix (Fin 2) (Fin 2) ℂ`. -/
theorem pauli_basis :
    LinearIndependent ℂ pauli ∧ Submodule.span ℂ (Set.range pauli) = ⊤ :=
  ⟨pauli_linearIndependent, pauli_span⟩

/-- The basis of `Matrix (Fin 2) (Fin 2) ℂ` given by the Pauli matrices. -/
noncomputable def pauliBasis : Module.Basis (Fin 4) ℂ (Matrix (Fin 2) (Fin 2) ℂ) :=
  Module.Basis.mk pauli_linearIndependent (le_of_eq pauli_span.symm)

@[simp] lemma coe_pauliBasis : ⇑pauliBasis = pauli := Module.Basis.coe_mk _ _

/-- Explicit expansion of an arbitrary 2×2 complex matrix in the Pauli basis. -/
theorem pauli_decomposition (M : Matrix (Fin 2) (Fin 2) ℂ) :
    M = ((M 0 0 + M 1 1) / 2) • pauliI + ((M 0 1 + M 1 0) / 2) • pauliX
      + (Complex.I * (M 0 1 - M 1 0) / 2) • pauliY + ((M 0 0 - M 1 1) / 2) • pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliI, pauliX, pauliY, pauliZ] <;>
    ring_nf <;>
    simp [Complex.I_sq] <;>
    ring

/-- Uniqueness of the coefficients in a Pauli expansion. -/
theorem pauli_coeff_unique {a b : Fin 4 → ℂ}
    (h : ∑ i, a i • pauli i = ∑ i, b i • pauli i) : a = b := by
  have hli := Fintype.linearIndependent_iff.mp pauli_linearIndependent
  funext i
  have h0 : ∑ i, (a i - b i) • pauli i = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, h, sub_self]
  exact sub_eq_zero.mp (hli (fun i => a i - b i) h0 i)

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

