/-
# Hermitian Real Spectrum
Category: Quantum Physics
Target: QPhys.hermitian_real_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hermitian Real Spectrum
Category: Quantum Physics
Target: QPhys.hermitian_real_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

namespace QPhys

open scoped ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- For a Hermitian (symmetric) operator `T` on a complex inner product space, an eigenvalue
equation `T v = μ • v` with `v ≠ 0` forces `μ` to be fixed by complex conjugation. -/

theorem hermitian_real_spectrum' {T : H →ₗ[ℂ] H} (hT : LinearMap.IsSymmetric T)
    {μ : ℂ} (hμ : Module.End.HasEigenvalue T μ) :
    μ.im = 0 := by
  obtain ⟨v, hv, hv0⟩ := hμ.exists_hasEigenvector
  exact (hermitian_real_spectrum hT hv0 (Module.End.mem_eigenspace_iff.mp hv)).1

end QPhys

