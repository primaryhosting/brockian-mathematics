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

/-- The Pauli matrix `σ₁ = X`. -/
def sigmaX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli matrix `σ₂ = Y`. -/
def sigmaY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- The Pauli matrix `σ₃ = Z`. -/
def sigmaZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The family `(I, X, Y, Z)` consisting of the identity matrix and the three Pauli
matrices, viewed as a family of `2 × 2` complex matrices indexed by `Fin 4`. -/
def pauli : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ := ![1, sigmaX, sigmaY, sigmaZ]

/-- The identity matrix together with the three Pauli matrices are linearly independent
over `ℂ`. -/
theorem linearIndependent_pauli : LinearIndependent ℂ pauli := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  -- Read off the four entries of the vanishing linear combination.
  have h00 := congr_fun (congr_fun hg 0) 0
  have h01 := congr_fun (congr_fun hg 0) 1
  have h10 := congr_fun (congr_fun hg 1) 0
  have h11 := congr_fun (congr_fun hg 1) 1
  simp [Fin.sum_univ_four, pauli, sigmaX, sigmaY, sigmaZ] at h00 h01 h10 h11
  -- `h00 : g 0 + g 3 = 0`, `h01 : g 1 - g 2 * I = 0`,
  -- `h10 : g 1 + g 2 * I = 0`, `h11 : g 0 - g 3 = 0`.
  have hg2 : g 2 * Complex.I = 0 := by linear_combination (h10 - h01) / 2
  have h2 : g 2 = 0 := (mul_eq_zero.mp hg2).resolve_right Complex.I_ne_zero
  have h0 : g 0 = 0 := by linear_combination (h00 + h11) / 2
  have h3 : g 3 = 0 := by linear_combination (h00 - h11) / 2
  have h1 : g 1 = 0 := by linear_combination (h01 + h10) / 2
  fin_cases i <;> assumption

/-- The space of `2 × 2` complex matrices has dimension `4` over `ℂ`. -/
theorem finrank_matrix_two : Module.finrank ℂ (Matrix (Fin 2) (Fin 2) ℂ) = 4 := by
  simp [Module.finrank_matrix]

/-- **The Pauli basis.** The identity matrix `I` together with the three Pauli matrices
`X`, `Y`, `Z` form a basis of the `ℂ`-vector space of `2 × 2` complex matrices. -/
theorem pauli_basis :
    ∃ b : Module.Basis (Fin 4) ℂ (Matrix (Fin 2) (Fin 2) ℂ), ⇑b = pauli := by
  refine ⟨basisOfLinearIndependentOfCardEqFinrank linearIndependent_pauli ?_, ?_⟩
  · simpa using finrank_matrix_two.symm
  · exact coe_basisOfLinearIndependentOfCardEqFinrank _ _

/-- Consequence: `{I, X, Y, Z}` spans the space of `2 × 2` complex matrices. -/
theorem span_pauli_eq_top :
    Submodule.span ℂ (Set.range pauli) = ⊤ := by
  obtain ⟨b, hb⟩ := pauli_basis
  rw [← hb, ← Module.Basis.span_eq b]

end QC

