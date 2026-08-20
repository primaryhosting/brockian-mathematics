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

/-!
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace QPhys

open scoped InnerProductSpace ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A (bounded, everywhere-defined) linear operator on a complex inner product space is
*symmetric* if it satisfies `⟪A u, v⟫ = ⟪u, A v⟫` for all vectors `u`, `v`. -/

theorem heisenberg_uncertainty {X P : H →ₗ[ℂ] H} {ψ : H} (hbar : ℝ)
    (hX : IsSymmetricOp X) (hP : IsSymmetricOp P) (hψ : ‖ψ‖ = 1)
    (hcomm : ⟪ψ, X (P ψ) - P (X ψ)⟫_ℂ = Complex.I * hbar) :
    spread X ψ * spread P ψ ≥ hbar / 2 := by
  set u : H := X ψ - ⟪ψ, X ψ⟫_ℂ • ψ with hu
  set v : H := P ψ - ⟪ψ, P ψ⟫_ℂ • ψ with hv
  have huv : ⟪u, v⟫_ℂ = ⟪ψ, X (P ψ)⟫_ℂ - ⟪ψ, X ψ⟫_ℂ * ⟪ψ, P ψ⟫_ℂ := inner_centered hX hψ
  have hvu : ⟪v, u⟫_ℂ = ⟪ψ, P (X ψ)⟫_ℂ - ⟪ψ, P ψ⟫_ℂ * ⟪ψ, X ψ⟫_ℂ := inner_centered hP hψ
  have hconj : ⟪v, u⟫_ℂ = conj ⟪u, v⟫_ℂ := (inner_conj_symm v u).symm
  have hdiff : ⟪u, v⟫_ℂ - conj ⟪u, v⟫_ℂ = Complex.I * hbar := by
    rw [← hconj, huv, hvu, ← hcomm, inner_sub_right]
    ring
  have him2 : (⟪v, u⟫_ℂ).im = -(⟪u, v⟫_ℂ).im := by
    rw [hconj, Complex.conj_im]
  have him : (⟪u, v⟫_ℂ).im = hbar / 2 := by
    have := congrArg Complex.im hdiff
    simp [Complex.sub_im, Complex.mul_im] at this
    linarith
  have h1 : |hbar / 2| ≤ ‖⟪u, v⟫_ℂ‖ := by
    rw [← him]
    exact Complex.abs_im_le_norm _
  have h2 : ‖⟪u, v⟫_ℂ‖ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm u v
  have : hbar / 2 ≤ |hbar / 2| := le_abs_self _
  simp only [spread, ← hu, ← hv, ge_iff_le]
  linarith

/-- `IsSymmetricOp` is exactly Mathlib's `LinearMap.IsSymmetric`. -/
