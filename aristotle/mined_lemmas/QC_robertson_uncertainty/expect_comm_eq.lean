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
