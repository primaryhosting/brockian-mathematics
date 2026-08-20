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

theorem pbr_theorem {Λ : Type*} [Fintype Λ]
    (μ : Qubit → Λ → ℝ) (ξ : Fin 4 → Λ → Λ → ℝ)
    (hμ : ∀ a l, 0 ≤ μ a l)
    (hξ : ∀ k l₁ l₂, 0 ≤ ξ k l₁ l₂)
    (hξsum : ∀ l₁ l₂, ∑ k, ξ k l₁ l₂ = 1)
    (hborn : ∀ j k : Fin 4,
      ∑ l₁, ∑ l₂, μ (prep j).1 l₁ * μ (prep j).2 l₂ * ξ k l₁ l₂
        = ‖ip (pbrBasis k) (tensor (prep j).1 (prep j).2)‖ ^ 2) :
    ∀ l : Λ, μ ket0 l = 0 ∨ μ ketPlus l = 0 := by
  intro l
  by_contra hcon
  push_neg at hcon
  obtain ⟨h0, hp⟩ := hcon
  have hp0 : 0 < μ ket0 l := lt_of_le_of_ne (hμ _ _) (Ne.symm h0)
  have hpp : 0 < μ ketPlus l := lt_of_le_of_ne (hμ _ _) (Ne.symm hp)
  have key : ∀ k : Fin 4, ξ k l l = 0 := by
    intro k
    have hb := hborn k k
    rw [pbrBasis_antidistinguishes k] at hb
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow] at hb
    fin_cases k <;>
      exact response_zero_at_overlap hμ hξ (by simpa [prep] using hb) (by assumption)
        (by assumption)
  have := hξsum l l
  rw [Finset.sum_congr rfl (fun k _ => key k)] at this
  simp at this

/-! ### Non-vacuity: the hypotheses of `pbr_theorem` are consistent -/

