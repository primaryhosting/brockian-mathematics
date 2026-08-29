import Mathlib

/-!
# Pauli Basis
Category: Quantum Computing
Target: QC.pauli_basis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace QC

/-- The 2×2 identity (Pauli `I`). -/
def pauliI : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 1]

/-- The Pauli `X` matrix. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli `Y` matrix. -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- The Pauli `Z` matrix. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The family `{I, X, Y, Z}` of Pauli matrices, indexed by `Fin 4`. -/
def pauli : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ := ![pauliI, pauliX, pauliY, pauliZ]

/-- Entrywise description of a linear combination of the Pauli matrices. -/
lemma pauli_comb (c : Fin 4 → ℂ) :
    ∑ i, c i • pauli i =
      !![c 0 + c 3, c 1 - Complex.I * c 2; c 1 + Complex.I * c 2, c 0 - c 3] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_four, pauli, pauliI, pauliX, pauliY, pauliZ] <;>
    ring

lemma pauli_linearIndependent : LinearIndependent ℂ pauli := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  rw [pauli_comb] at hc
  have h00 : c 0 + c 3 = 0 := by
    have := congrFun (congrFun hc 0) 0; simpa using this
  have h11 : c 0 - c 3 = 0 := by
    have := congrFun (congrFun hc 1) 1; simpa using this
  have h01 : c 1 - Complex.I * c 2 = 0 := by
    have := congrFun (congrFun hc 0) 1; simpa using this
  have h10 : c 1 + Complex.I * c 2 = 0 := by
    have := congrFun (congrFun hc 1) 0; simpa using this
  have hc0 : c 0 = 0 := by linear_combination (h00 + h11) / 2
  have hc3 : c 3 = 0 := by linear_combination (h00 - h11) / 2
  have hc1 : c 1 = 0 := by linear_combination (h01 + h10) / 2
  have hc2 : c 2 = 0 := by
    have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
    have : Complex.I * c 2 = 0 := by linear_combination (h10 - h01) / 2
    exact (mul_eq_zero.1 this).resolve_left hI
  fin_cases i <;> assumption

lemma pauli_span : Submodule.span ℂ (Set.range pauli) = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun M => ?_
  set c : Fin 4 → ℂ :=
    ![(M 0 0 + M 1 1) / 2, (M 0 1 + M 1 0) / 2,
      Complex.I * (M 0 1 - M 1 0) / 2, (M 0 0 - M 1 1) / 2] with hcdef
  have hc0 : c 0 = (M 0 0 + M 1 1) / 2 := by rw [hcdef]; rfl
  have hc1 : c 1 = (M 0 1 + M 1 0) / 2 := by rw [hcdef]; rfl
  have hc2 : c 2 = Complex.I * (M 0 1 - M 1 0) / 2 := by rw [hcdef]; rfl
  have hc3 : c 3 = (M 0 0 - M 1 1) / 2 := by rw [hcdef]; rfl
  have e00 : c 0 + c 3 = M 0 0 := by rw [hc0, hc3]; ring
  have e11 : c 0 - c 3 = M 1 1 := by rw [hc0, hc3]; ring
  have e01 : c 1 - Complex.I * c 2 = M 0 1 := by
    rw [hc1, hc2]; linear_combination ((M 1 0 - M 0 1) / 2) * Complex.I_sq
  have e10 : c 1 + Complex.I * c 2 = M 1 0 := by
    rw [hc1, hc2]; linear_combination ((M 0 1 - M 1 0) / 2) * Complex.I_sq
  have hM : M = ∑ i, c i • pauli i := by
    rw [pauli_comb, e00, e01, e10, e11]
    exact (Matrix.etaExpand_eq M).symm
  rw [hM]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span ⟨i, rfl⟩

/-- The Pauli matrices `{I, X, Y, Z}` form a basis of the ℂ-vector space of
2×2 complex matrices. -/
noncomputable def pauliBasis : Module.Basis (Fin 4) ℂ (Matrix (Fin 2) (Fin 2) ℂ) :=
  Module.Basis.mk pauli_linearIndependent (le_of_eq pauli_span.symm)

@[simp] lemma coe_pauliBasis : ⇑pauliBasis = pauli := Module.Basis.coe_mk _ _

/-- **Pauli basis.** The four Pauli matrices `I, X, Y, Z` are linearly independent over `ℂ`
and span the space of 2×2 complex matrices; hence they form a basis, witnessed by
`QC.pauliBasis`. -/
theorem pauli_basis :
    LinearIndependent ℂ pauli ∧ Submodule.span ℂ (Set.range pauli) = ⊤ ∧
      ∃ B : Module.Basis (Fin 4) ℂ (Matrix (Fin 2) (Fin 2) ℂ), ⇑B = pauli :=
  ⟨pauli_linearIndependent, pauli_span, pauliBasis, coe_pauliBasis⟩

end QC

