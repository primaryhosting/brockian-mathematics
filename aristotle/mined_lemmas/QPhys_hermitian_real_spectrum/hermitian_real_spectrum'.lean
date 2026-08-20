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

theorem hermitian_real_spectrum' {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) {μ : ℂ}
    (hμ : Module.End.HasEigenvalue T μ) : ∃ r : ℝ, μ = (r : ℂ) := by
  obtain ⟨v, hv₁, hv₂⟩ := hμ.exists_hasEigenvector
  exact hermitian_real_spectrum hT hv₂ (Module.End.mem_eigenspace_iff.mp hv₁)

/-- Corollary for bounded (continuous) self-adjoint operators, the usual setting for
quantum-mechanical observables: every eigenvalue is real. -/
