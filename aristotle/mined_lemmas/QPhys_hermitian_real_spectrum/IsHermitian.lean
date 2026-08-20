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

def IsHermitian (T : E →ₗ[ℂ] E) : Prop :=
  ∀ x y : E, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ

/-- `μ` is an eigenvalue of `T` if there is a nonzero vector `v` with `T v = μ • v`. -/
