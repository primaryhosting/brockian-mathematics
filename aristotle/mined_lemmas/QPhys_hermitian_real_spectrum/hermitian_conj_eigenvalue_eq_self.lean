/-
/-!
# Hermitian Real Spectrum
Category: Quantum Physics
Target: QPhys.hermitian_real_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

/-!
# Hermitian Real Spectrum
Category: Quantum Physics
Target: QPhys.hermitian_real_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace QPhys

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- An operator `A` on a complex inner product space is *Hermitian* if
`⟪A x, y⟫ = ⟪x, A y⟫` for all vectors `x, y`. -/

theorem hermitian_conj_eigenvalue_eq_self
    {A : E →ₗ[ℂ] E} (hA : IsHermitian A) {μ : ℂ} {v : E} (hv : v ≠ 0)
    (heig : A v = μ • v) : (starRingEnd ℂ) μ = μ := by
  have hvv : ⟪v, v⟫_ℂ ≠ 0 := by
    simpa [inner_self_eq_zero] using hv
  have key : (starRingEnd ℂ) μ * ⟪v, v⟫_ℂ = μ * ⟪v, v⟫_ℂ := by
    have h1 : ⟪A v, v⟫_ℂ = (starRingEnd ℂ) μ * ⟪v, v⟫_ℂ := by
      rw [heig, inner_smul_left]
    have h2 : ⟪v, A v⟫_ℂ = μ * ⟪v, v⟫_ℂ := by
      rw [heig, inner_smul_right]
    rw [← h1, ← h2]
    exact hA v v
  exact mul_right_cancel₀ hvv key

/-- **Every eigenvalue of a Hermitian operator is real.**
If `A` is a Hermitian operator on a complex inner product space and `v ≠ 0`
satisfies `A v = μ • v`, then `μ` is a real number. -/
