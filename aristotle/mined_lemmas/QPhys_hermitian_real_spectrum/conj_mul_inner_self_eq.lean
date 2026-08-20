import Mathlib

/-!
# Hermitian Real Spectrum
Category: Quantum Physics
Target: QPhys.hermitian_real_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped InnerProductSpace

namespace QPhys

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A linear operator on a complex inner product space is *Hermitian* if it is symmetric
with respect to the inner product: `⟪T x, y⟫ = ⟪x, T y⟫` for all `x`, `y`. -/

theorem conj_mul_inner_self_eq (T : E →ₗ[ℂ] E) (hT : IsHermitian T) {μ : ℂ} {v : E}
    (hv : T v = μ • v) :
    (starRingEnd ℂ) μ * ⟪v, v⟫_ℂ = μ * ⟪v, v⟫_ℂ := by
  have h := hT v v
  rw [hv] at h
  rwa [inner_smul_left, inner_smul_right] at h

/-- **Every eigenvalue of a Hermitian operator is real.** -/
