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

namespace QC

/-- The identity Pauli matrix `I` (often written `σ₀`). -/
def pauliI : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 1]

/-- The Pauli matrix `X`. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli matrix `Y`. -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- The Pauli matrix `Z`. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The family of the four Pauli matrices `I, X, Y, Z`. -/
def pauli : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ := ![pauliI, pauliX, pauliY, pauliZ]

lemma pauli_linearIndependent : LinearIndependent ℂ pauli := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h00 := congrFun (congrFun hg 0) 0
  have h01 := congrFun (congrFun hg 0) 1
  have h10 := congrFun (congrFun hg 1) 0
  have h11 := congrFun (congrFun hg 1) 1
  simp [pauli, pauliI, pauliX, pauliY, pauliZ, Fin.sum_univ_four,
    Matrix.add_apply] at h00 h01 h10 h11
  have hg0 : g 0 = 0 := by linear_combination (h00 + h11) / 2
  have hg3 : g 3 = 0 := by linear_combination (h00 - h11) / 2
  have hg1 : g 1 = 0 := by linear_combination (h01 + h10) / 2
  have hg2 : g 2 = 0 := by
    have h : (g 2) * (-2 * Complex.I) = 0 := by linear_combination h01 - h10
    rcases mul_eq_zero.mp h with h' | h'
    · exact h'
    · exact absurd h' (by simp [Complex.I_ne_zero])
  fin_cases i <;> assumption

lemma pauli_span : Submodule.span ℂ (Set.range pauli) = ⊤ := by
  rw [eq_top_iff]
  rintro M -
  have hmem : ∀ i : Fin 4, pauli i ∈ Submodule.span ℂ (Set.range pauli) := fun i =>
    Submodule.subset_span ⟨i, rfl⟩
  have key : M = ((M 0 0 + M 1 1) / 2) • pauli 0 + ((M 0 1 + M 1 0) / 2) • pauli 1
      + (Complex.I * (M 0 1 - M 1 0) / 2) • pauli 2 + ((M 0 0 - M 1 1) / 2) • pauli 3 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pauli, pauliI, pauliX, pauliY, pauliZ, Matrix.add_apply] <;>
      field_simp <;> ring_nf <;> simp [Complex.I_sq] <;> ring
  rw [key]
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.smul_mem _ _ (hmem 0)) (Submodule.smul_mem _ _ (hmem 1)))
    (Submodule.smul_mem _ _ (hmem 2))) (Submodule.smul_mem _ _ (hmem 3))

/-- **The Pauli matrices form a basis.** The family `{I, X, Y, Z}` is a basis of the
`ℂ`-vector space of `2 × 2` complex matrices: it is linearly independent and spans. -/
theorem pauli_basis :
    LinearIndependent ℂ pauli ∧ Submodule.span ℂ (Set.range pauli) = ⊤ :=
  ⟨pauli_linearIndependent, pauli_span⟩

/-- The basis of `2 × 2` complex matrices given by the Pauli matrices `I, X, Y, Z`. -/
noncomputable def pauliBasis : Module.Basis (Fin 4) ℂ (Matrix (Fin 2) (Fin 2) ℂ) :=
  Module.Basis.mk pauli_linearIndependent (le_of_eq pauli_span.symm)

@[simp] lemma pauliBasis_apply (i : Fin 4) : pauliBasis i = pauli i := by
  simp [pauliBasis]

end QC

