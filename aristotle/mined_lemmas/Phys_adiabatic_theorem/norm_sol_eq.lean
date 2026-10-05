import Mathlib

/-!
# Adiabatic Theorem
Category: Frontier Phys
Target: Phys.adiabatic_theorem
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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types false
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Phys

open Complex MeasureTheory intervalIntegral
open scoped InnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ## Phases -/

/-- The unimodular phase `u ↦ exp (i r u)`. -/

theorem norm_sol_eq [CompleteSpace E] (P : ℝ → E →L[ℂ] E) (e₁ e₂ ε : ℝ)
    (hsa : ∀ s, IsSelfAdjoint (P s)) (ψ : ℝ → E)
    (hψ : ∀ s, HasDerivAt ψ ((-Complex.I / (ε : ℂ)) • (ham P e₁ e₂ s (ψ s))) s) (s : ℝ) :
    ‖ψ s‖ = ‖ψ 0‖ := by
  set c : ℂ := -Complex.I / (ε : ℂ) with hc
  have hconj : (starRingEnd ℂ) c + c = 0 := by
    simp [hc, div_eq_mul_inv, map_mul, Complex.conj_I]
  have hd : ∀ t : ℝ, HasDerivAt (fun t => ⟪ψ t, ψ t⟫_ℂ) 0 t := by
    intro t
    have hi := (hψ t).inner ℂ (hψ t)
    have hz : ⟪ψ t, c • ham P e₁ e₂ t (ψ t)⟫_ℂ + ⟪c • ham P e₁ e₂ t (ψ t), ψ t⟫_ℂ = 0 := by
      rw [inner_smul_right, inner_smul_left]
      have h1 : ⟪ham P e₁ e₂ t (ψ t), ψ t⟫_ℂ = ⟪ψ t, ham P e₁ e₂ t (ψ t)⟫_ℂ :=
        ham_symm P e₁ e₂ t (hsa t) _ _
      have h2 : (starRingEnd ℂ) c * ⟪ψ t, ham P e₁ e₂ t (ψ t)⟫_ℂ
            + c * ⟪ψ t, ham P e₁ e₂ t (ψ t)⟫_ℂ
          = ((starRingEnd ℂ) c + c) * ⟪ψ t, ham P e₁ e₂ t (ψ t)⟫_ℂ := by ring
      rw [h1, add_comm, h2, hconj, zero_mul]
    rw [hz] at hi
    exact hi
  have hconstf : ∀ x y : ℝ, (fun t => ⟪ψ t, ψ t⟫_ℂ) x = (fun t => ⟪ψ t, ψ t⟫_ℂ) y :=
    is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv)
  have hxy := hconstf s 0
  simp only [] at hxy
  have h1 : (‖ψ s‖ : ℝ) ^ 2 = (‖ψ 0‖ : ℝ) ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (ψ s), inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (ψ 0)] at hxy
    exact_mod_cast hxy
  nlinarith [norm_nonneg (ψ s), norm_nonneg (ψ 0)]

/-! ## The two phase-corrected components of the state -/

/-- Phase-corrected component of the state inside the instantaneous eigenspace. -/
