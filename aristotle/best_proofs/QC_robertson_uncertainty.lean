import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

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

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The expectation value `⟨A⟩_ψ = ⟪ψ, A ψ⟫` of an operator `A` in the state `ψ`. -/
noncomputable def expect (A : H →ₗ[ℂ] H) (ψ : H) : ℂ := ⟪ψ, A ψ⟫_ℂ

/-- The standard deviation (uncertainty) `ΔA = ‖(A - ⟨A⟩) ψ‖` of `A` in the state `ψ`. -/
noncomputable def Delta (A : H →ₗ[ℂ] H) (ψ : H) : ℝ := ‖A ψ - expect A ψ • ψ‖

/-- The commutator `[A, B] = A B - B A`. -/
noncomputable def comm (A B : H →ₗ[ℂ] H) : H →ₗ[ℂ] H := A ∘ₗ B - B ∘ₗ A

/-- `A` is symmetric (self-adjoint on its whole domain). -/
def IsSymm (A : H →ₗ[ℂ] H) : Prop := ∀ x y : H, ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ

/-- Expectation values of a symmetric operator are real. -/
lemma conj_expect_of_isSymm {A : H →ₗ[ℂ] H} (hA : IsSymm A) (ψ : H) :
    (starRingEnd ℂ) (expect A ψ) = expect A ψ := by
  rw [expect, inner_conj_symm]
  exact hA ψ ψ

/-- Key identity: the expectation of the commutator equals `⟪u, v⟫ - ⟪v, u⟫` for the
centered vectors `u = (A - ⟨A⟩)ψ`, `v = (B - ⟨B⟩)ψ`. -/
lemma expect_comm_eq {A B : H →ₗ[ℂ] H} (hA : IsSymm A) (hB : IsSymm B) {ψ : H}
    (hψ : ‖ψ‖ = 1) :
    expect (comm A B) ψ =
      ⟪A ψ - expect A ψ • ψ, B ψ - expect B ψ • ψ⟫_ℂ -
      ⟪B ψ - expect B ψ • ψ, A ψ - expect A ψ • ψ⟫_ℂ := by
  have hnorm : ⟪ψ, ψ⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ), hψ]
    norm_num
  set a : ℂ := expect A ψ
  set b : ℂ := expect B ψ
  have haA : ⟪A ψ, ψ⟫_ℂ = a := by rw [hA ψ ψ]; rfl
  have hbB : ⟪B ψ, ψ⟫_ℂ = b := by rw [hB ψ ψ]; rfl
  have hadef : ⟪ψ, A ψ⟫_ℂ = a := rfl
  have hbdef : ⟪ψ, B ψ⟫_ℂ = b := rfl
  have hca : (starRingEnd ℂ) a = a := conj_expect_of_isSymm hA ψ
  have hcb : (starRingEnd ℂ) b = b := conj_expect_of_isSymm hB ψ
  have h1 : ⟪A ψ - a • ψ, B ψ - b • ψ⟫_ℂ = ⟪ψ, A (B ψ)⟫_ℂ - a * b := by
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      hca, haA, hbdef, hnorm, hA ψ (B ψ)]
    ring
  have h2 : ⟪B ψ - b • ψ, A ψ - a • ψ⟫_ℂ = ⟪ψ, B (A ψ)⟫_ℂ - b * a := by
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      hcb, hbB, hadef, hnorm, hB ψ (A ψ)]
    ring
  rw [h1, h2, expect, comm]
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, inner_sub_right]
  ring

/-- **Robertson uncertainty relation.**  For symmetric operators `A`, `B` and a unit vector
`ψ`, the product of the uncertainties `ΔA · ΔB` is at least `½ |⟨[A, B]⟩|`. -/
theorem robertson_uncertainty {A B : H →ₗ[ℂ] H} (hA : IsSymm A) (hB : IsSymm B) {ψ : H}
    (hψ : ‖ψ‖ = 1) :
    Delta A ψ * Delta B ψ ≥ (1 / 2) * ‖expect (comm A B) ψ‖ := by
  set u : H := A ψ - expect A ψ • ψ with hu
  set v : H := B ψ - expect B ψ • ψ with hv
  have key : expect (comm A B) ψ = ⟪u, v⟫_ℂ - ⟪v, u⟫_ℂ := expect_comm_eq hA hB hψ
  have h1 : ‖⟪u, v⟫_ℂ‖ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm u v
  have h2 : ‖⟪v, u⟫_ℂ‖ ≤ ‖v‖ * ‖u‖ := norm_inner_le_norm v u
  have h3 : ‖expect (comm A B) ψ‖ ≤ 2 * (‖u‖ * ‖v‖) := by
    rw [key]
    calc ‖⟪u, v⟫_ℂ - ⟪v, u⟫_ℂ‖ ≤ ‖⟪u, v⟫_ℂ‖ + ‖⟪v, u⟫_ℂ‖ := norm_sub_le _ _
      _ ≤ ‖u‖ * ‖v‖ + ‖v‖ * ‖u‖ := add_le_add h1 h2
      _ = 2 * (‖u‖ * ‖v‖) := by ring
  have : Delta A ψ * Delta B ψ = ‖u‖ * ‖v‖ := rfl
  rw [ge_iff_le, this]
  linarith

end QC

