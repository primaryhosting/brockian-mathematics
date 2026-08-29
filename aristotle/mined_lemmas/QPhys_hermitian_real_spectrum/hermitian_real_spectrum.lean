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

theorem hermitian_real_spectrum {T : H →ₗ[ℂ] H} (hT : LinearMap.IsSymmetric T)
    {μ : ℂ} {v : H} (hv : v ≠ 0) (hTv : T v = μ • v) :
    μ.im = 0 ∧ ∃ r : ℝ, μ = (r : ℂ) := by
  have h := conj_eq_of_eigen hT hv hTv
  have him : μ.im = 0 := by
    have := congrArg Complex.im h
    simp only [Complex.conj_im] at this
    linarith
  exact ⟨him, ⟨μ.re, by apply Complex.ext <;> simp [him]⟩⟩

/-- Version phrased with `Module.End.HasEigenvalue`. -/
