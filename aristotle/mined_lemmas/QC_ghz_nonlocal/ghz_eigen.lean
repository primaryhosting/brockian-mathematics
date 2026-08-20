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

open Matrix
open scoped Kronecker

/-- Index type for three qubits. -/
abbrev Idx : Type := (Fin 2 × Fin 2) × Fin 2

/-- A measurement setting for one party: `false` means measure the Pauli `X`
observable, `true` means measure the Pauli `Y` observable. -/
abbrev Setting : Type := Bool

/-- The Pauli `X` matrix. -/

theorem ghz_eigen (s₁ s₂ s₃ : Setting) (h : merminContext s₁ s₂ s₃) :
    (triObs s₁ s₂ s₃).mulVec ghz = ((merminSign s₁ s₂ s₃ : ℤ) : ℂ) • ghz := by
  have compute : ∀ s₁ s₂ s₃ : Setting,
      (s₁ = false ∧ s₂ = false ∧ s₃ = false) ∨ (s₁ = false ∧ s₂ = true ∧ s₃ = true) ∨
        (s₁ = true ∧ s₂ = false ∧ s₃ = true) ∨ (s₁ = true ∧ s₂ = true ∧ s₃ = false) →
      (triObs s₁ s₂ s₃).mulVec ghz = ((merminSign s₁ s₂ s₃ : ℤ) : ℂ) • ghz := by
    rintro s₁ s₂ s₃ (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;>
      · funext i
        fin_cases i <;>
          simp [triObs, obs, merminSign, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
            Fin.sum_univ_two, ghz, pauliX, pauliY]
  refine compute s₁ s₂ s₃ ?_
  revert h
  cases s₁ <;> cases s₂ <;> cases s₃ <;> simp [merminContext]

/-- Product of the four Mermin eigenvalues is `-1`. -/
