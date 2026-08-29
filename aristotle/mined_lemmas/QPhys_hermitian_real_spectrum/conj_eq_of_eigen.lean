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

theorem conj_eq_of_eigen {T : H →ₗ[ℂ] H} (hT : LinearMap.IsSymmetric T)
    {μ : ℂ} {v : H} (hv : v ≠ 0) (hTv : T v = μ • v) :
    conj μ = μ := by
  have key : conj μ * (inner ℂ v v : ℂ) = μ * (inner ℂ v v : ℂ) := by
    have h1 : (inner ℂ (T v) v : ℂ) = (inner ℂ v (T v) : ℂ) := hT v v
    rw [hTv, inner_smul_left, inner_smul_right] at h1
    exact h1
  have hvv : (inner ℂ v v : ℂ) ≠ 0 := by
    simpa [inner_self_eq_zero] using hv
  exact mul_right_cancel₀ hvv key

/-- **Hermitian operators have real spectrum.** If `T` is a Hermitian operator on a complex
inner product space and `μ` is an eigenvalue of `T` (i.e. `T v = μ • v` for some nonzero `v`),
then `μ` is real: its imaginary part vanishes, and it is the coercion of a real number. -/
