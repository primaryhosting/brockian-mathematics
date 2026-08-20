/-
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace QI

/-! ### Two-qubit vectors, inner products and the states involved -/

/-- A (pure) qubit state vector. -/
abbrev Qubit := Fin 2 → ℂ

/-- A two-qubit state vector, written in curried form. -/
abbrev TwoQubit := Fin 2 → Fin 2 → ℂ

/-- The product (tensor) of two qubit vectors. -/

theorem exists_pbr_model :
    ∃ (μ : Qubit → Fin 2 → ℝ) (ξ : Fin 4 → Fin 2 → Fin 2 → ℝ),
      (∀ a l, 0 ≤ μ a l) ∧ (∀ k l₁ l₂, 0 ≤ ξ k l₁ l₂) ∧ (∀ l₁ l₂, ∑ k, ξ k l₁ l₂ = 1) ∧
      (∀ j k : Fin 4, ∑ l₁, ∑ l₂, μ (prep j).1 l₁ * μ (prep j).2 l₂ * ξ k l₁ l₂
        = ‖ip (pbrBasis k) (tensor (prep j).1 (prep j).2)‖ ^ 2) := by
  refine ⟨fun a l => if a = st l then 1 else 0,
    fun k l₁ l₂ => ‖ip (pbrBasis k) (tensor (st l₁) (st l₂))‖ ^ 2, ?_, ?_, pbr_born_sum_one, ?_⟩
  · intro a l; dsimp only; split <;> norm_num
  · intro k l₁ l₂; positivity
  · intro j k
    fin_cases j <;>
      simp [prep, st, Fin.sum_univ_two, ket0_ne_ketPlus, ket0_ne_ketPlus.symm]

end QI

#print axioms QI.pbr_theorem
#print axioms QI.exists_pbr_model
#print axioms QI.pbrBasis_orthonormal

