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

namespace QPhys

local notation "⟪" x ", " y "⟫" => inner ℂ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- An operator `A` on a complex inner product space is *symmetric* (formally self-adjoint)
when `⟪A x, y⟫ = ⟪x, A y⟫` for all `x, y`. -/

lemma inner_shift_sub_conj {A B : E →ₗ[ℂ] E} (hA : IsSymmetricOp A) (hB : IsSymmetricOp B)
    (ψ : E) (a b : ℝ) :
    ⟪A ψ - (a : ℂ) • ψ, B ψ - (b : ℂ) • ψ⟫ - ⟪B ψ - (b : ℂ) • ψ, A ψ - (a : ℂ) • ψ⟫
      = ⟪ψ, A (B ψ) - B (A ψ)⟫ := by
  have hAB : ⟪A ψ, B ψ⟫ = ⟪ψ, A (B ψ)⟫ := hA ψ (B ψ)
  have hBA : ⟪B ψ, A ψ⟫ = ⟪ψ, B (A ψ)⟫ := hB ψ (A ψ)
  have hAs : ⟪A ψ, ψ⟫ = ⟪ψ, A ψ⟫ := hA ψ ψ
  have hBs : ⟪B ψ, ψ⟫ = ⟪ψ, B ψ⟫ := hB ψ ψ
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal]
  rw [hAB, hBA, hAs, hBs]
  ring

/-- **Robertson uncertainty relation.**

For symmetric operators `A`, `B` on a complex inner product space and any state `ψ`,
`|⟪ψ, [A, B] ψ⟫| ≤ 2 · Δ A · Δ B`. -/
