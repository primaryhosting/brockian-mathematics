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

def HasEigenvalue (T : E →ₗ[ℂ] E) (μ : ℂ) : Prop :=
  ∃ v : E, v ≠ 0 ∧ T v = μ • v

/-- Key intermediate lemma: for a Hermitian operator `T` and an eigenvector `v` with
eigenvalue `μ`, the two ways of evaluating `⟪T v, v⟫` give
`conj μ * ⟪v, v⟫ = μ * ⟪v, v⟫`. -/
