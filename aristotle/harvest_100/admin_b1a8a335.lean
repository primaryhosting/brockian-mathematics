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

/-- The indexed family `{I, X, Y, Z}` of Pauli matrices. -/
def pauli : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => pauliI
  | 1 => pauliX
  | 2 => pauliY
  | 3 => pauliZ

/-- Every `2 × 2` complex matrix is the (explicit) linear combination
`((M 0 0 + M 1 1)/2) • I + ((M 0 1 + M 1 0)/2) • X + (I*(M 0 1 - M 1 0)/2) • Y +
 ((M 0 0 - M 1 1)/2) • Z` of the Pauli matrices. -/
theorem pauli_expansion (M : Matrix (Fin 2) (Fin 2) ℂ) :
    M = ((M 0 0 + M 1 1) / 2) • pauli 0 + ((M 0 1 + M 1 0) / 2) • pauli 1
      + (Complex.I * (M 0 1 - M 1 0) / 2) • pauli 2 + ((M 0 0 - M 1 1) / 2) • pauli 3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauli, pauliI, pauliX, pauliY, pauliZ, Complex.ext_iff] <;> ring_nf <;> simp

/-- The Pauli matrices are linearly independent over `ℂ`. -/
theorem pauli_linearIndependent : LinearIndependent ℂ pauli := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  rw [Fin.sum_univ_four] at hg
  have h00 := congrFun (congrFun hg 0) 0
  have h01 := congrFun (congrFun hg 0) 1
  have h10 := congrFun (congrFun hg 1) 0
  have h11 := congrFun (congrFun hg 1) 1
  simp [pauli, pauliI, pauliX, pauliY, pauliZ] at h00 h01 h10 h11
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hg0 : g 0 = 0 := by
    have : g 0 + g 3 = 0 := h00
    have h2 : g 0 - g 3 = 0 := by linear_combination h11
    linear_combination (this + h2) / 2
  have hg3 : g 3 = 0 := by
    have : g 0 + g 3 = 0 := h00
    linear_combination this - hg0
  have hg1 : g 1 = 0 := by
    have hsum : (g 1 - Complex.I * g 2) + (g 1 + Complex.I * g 2) = 0 := by
      linear_combination h01 + h10
    linear_combination hsum / 2
  have hg2 : g 2 = 0 := by
    have hdiff : Complex.I * g 2 = 0 := by linear_combination (h10 - h01) / 2
    exact (mul_eq_zero.mp hdiff).resolve_left hI
  fin_cases i <;> assumption

/-- The Pauli matrices span the space of `2 × 2` complex matrices. -/
theorem pauli_span : Submodule.span ℂ (Set.range pauli) = ⊤ := by
  refine top_unique fun M _ => ?_
  rw [pauli_expansion M]
  have hmem : ∀ i : Fin 4, pauli i ∈ Submodule.span ℂ (Set.range pauli) := fun i =>
    Submodule.subset_span ⟨i, rfl⟩
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.smul_mem _ _ (hmem 0)) (Submodule.smul_mem _ _ (hmem 1)))
    (Submodule.smul_mem _ _ (hmem 2))) (Submodule.smul_mem _ _ (hmem 3))

/-- **The Pauli matrices `{I, X, Y, Z}` form a basis of the `ℂ`-vector space of
`2 × 2` complex matrices.** -/
theorem pauli_basis :
    ∃ b : Module.Basis (Fin 4) ℂ (Matrix (Fin 2) (Fin 2) ℂ), ⇑b = pauli :=
  ⟨Module.Basis.mk pauli_linearIndependent (le_of_eq pauli_span.symm),
    funext (Module.Basis.mk_apply _ _)⟩

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

