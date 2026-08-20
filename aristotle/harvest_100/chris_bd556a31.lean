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

/-
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QPhys

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The spread (standard deviation) of the observable `A` in the state `ψ`:
the norm of `A ψ` after subtracting its expectation value `⟪ψ, A ψ⟫`. -/
noncomputable def spread (A : H →ₗ[ℂ] H) (ψ : H) : ℝ :=
  ‖A ψ - (inner ℂ ψ (A ψ)) • ψ‖

/-- **Heisenberg uncertainty principle.**  If `X` and `P` are symmetric operators on a
complex inner product space satisfying the canonical commutation relation
`X P ψ - P X ψ = i ħ ψ` at a normalized state `ψ`, then the product of the spreads of
`X` and `P` in the state `ψ` is at least `ħ / 2`. -/
theorem heisenberg_uncertainty (X P : H →ₗ[ℂ] H)
    (hX : ∀ x y : H, inner ℂ (X x) y = inner ℂ x (X y))
    (hP : ∀ x y : H, inner ℂ (P x) y = inner ℂ x (P y))
    (ψ : H) (hψ : ‖ψ‖ = 1) (ħ : ℝ)
    (hcomm : X (P ψ) - P (X ψ) = (Complex.I * ħ) • ψ) :
    spread X ψ * spread P ψ ≥ ħ / 2 := by
  set a : ℂ := inner ℂ ψ (X ψ) with ha
  set b : ℂ := inner ℂ ψ (P ψ) with hb
  set u : H := X ψ - a • ψ with hu
  set v : H := P ψ - b • ψ with hv
  have hnn : (inner ℂ ψ ψ : ℂ) = 1 := by
    simp [inner_self_eq_norm_sq_to_K, hψ]
  have hXψ : (inner ℂ (X ψ) ψ : ℂ) = a := by rw [hX, ha]
  have hPψ : (inner ℂ (P ψ) ψ : ℂ) = b := by rw [hP, hb]
  have huv : (inner ℂ u v : ℂ) = inner ℂ (X ψ) (P ψ) - a * b := by
    simp only [hu, hv, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      hnn, hXψ, ha, hb]
    ring
  have hvu : (inner ℂ v u : ℂ) = inner ℂ (P ψ) (X ψ) - b * a := by
    simp only [hu, hv, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      hnn, hPψ, ha, hb]
    ring
  have hdiff : (inner ℂ u v : ℂ) - inner ℂ v u = Complex.I * ħ := by
    rw [huv, hvu]
    have h1 : (inner ℂ (X ψ) (P ψ) : ℂ) = inner ℂ ψ (X (P ψ)) := hX ψ (P ψ)
    have h2 : (inner ℂ (P ψ) (X ψ) : ℂ) = inner ℂ ψ (P (X ψ)) := hP ψ (X ψ)
    have h3 : (inner ℂ ψ (X (P ψ)) : ℂ) - inner ℂ ψ (P (X ψ)) = Complex.I * ħ := by
      rw [← inner_sub_right, hcomm, inner_smul_right, hnn, mul_one]
    rw [h1, h2]
    rw [show (inner ℂ ψ (X (P ψ)) : ℂ) - a * b - (inner ℂ ψ (P (X ψ)) - b * a)
        = (inner ℂ ψ (X (P ψ)) : ℂ) - inner ℂ ψ (P (X ψ)) by ring, h3]
  have hconj : (inner ℂ v u : ℂ) = starRingEnd ℂ (inner ℂ u v) :=
    (inner_conj_symm (𝕜 := ℂ) v u).symm
  have him : (inner ℂ u v : ℂ).im = ħ / 2 := by
    rw [hconj, Complex.sub_conj] at hdiff
    have := congrArg Complex.im hdiff
    simp at this ⊢
    linarith [this]
  have hle : (inner ℂ u v : ℂ).im ≤ ‖(inner ℂ u v : ℂ)‖ := Complex.im_le_norm _
  have hcs : ‖(inner ℂ u v : ℂ)‖ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm u v
  have : ħ / 2 ≤ ‖u‖ * ‖v‖ := by rw [← him]; linarith
  simpa [spread, hu, hv, ha, hb, ge_iff_le] using this

end QPhys

