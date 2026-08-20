import Mathlib

/-!
# Hermitian Real Spectrum
Category: Quantum Physics
Target: QPhys.hermitian_real_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

open scoped InnerProductSpace
open RCLike

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Every eigenvalue of a Hermitian operator is real.**

`T : E →ₗ[ℂ] E` is Hermitian (symmetric): `⟪T x, y⟫ = ⟪x, T y⟫` for all `x y`.
If `μ : ℂ` is an eigenvalue of `T`, i.e. there is a nonzero `v` with `T v = μ • v`,
then `μ` is real: `μ = (r : ℂ)` for some `r : ℝ`. -/

theorem selfAdjoint_real_spectrum [CompleteSpace E] {T : E →L[ℂ] E} (hT : IsSelfAdjoint T)
    {μ : ℂ} {v : E} (hv : v ≠ 0) (heig : T v = μ • v) : ∃ r : ℝ, μ = (r : ℂ) :=
  hermitian_real_spectrum hT.isSymmetric hv heig

/-- Corollary for Hermitian matrices: every eigenvalue of a Hermitian matrix is real. -/
