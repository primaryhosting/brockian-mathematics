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

/-- **Hermitian operators have real spectrum.**

Let `T` be a Hermitian (symmetric / self-adjoint) linear operator on a complex inner product
space `E`, i.e. `⟪T x, y⟫ = ⟪x, T y⟫` for all `x y`.  If `mu : ℂ` is an eigenvalue of `T`,
witnessed by a nonzero eigenvector `v` with `T v = mu • v`, then `mu` is real: its imaginary
part vanishes (equivalently, `conj mu = mu`).

The proof is the standard one: `⟪T v, v⟫ = ⟪v, T v⟫` gives
`conj mu * ⟪v, v⟫ = mu * ⟪v, v⟫`, and `⟪v, v⟫ ≠ 0` since `v ≠ 0`. -/
theorem hermitian_real_spectrum {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →ₗ[ℂ] E) (hT : ∀ x y : E, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ)
    (mu : ℂ) (v : E) (hv : v ≠ 0) (hev : T v = mu • v) :
    mu.im = 0 ∧ (starRingEnd ℂ) mu = mu := by
  have hvv : (⟪v, v⟫_ℂ) ≠ 0 := by
    simpa [inner_self_eq_zero] using hv
  have h := hT v v
  rw [hev, inner_smul_left, inner_smul_right] at h
  field_simp at h
  refine ⟨?_, h⟩
  have := congrArg Complex.im h
  have h2 : -mu.im = mu.im := by simpa [Complex.conj_im] using this
  linarith

/-- Reformulation in terms of Mathlib's `Module.End.HasEigenvalue`: every eigenvalue of a
symmetric (Hermitian) operator on a complex inner product space is real. -/
theorem hermitian_real_spectrum' {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →ₗ[ℂ] E) (hT : ∀ x y : E, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ)
    (mu : ℂ) (hmu : Module.End.HasEigenvalue T mu) :
    mu.im = 0 := by
  obtain ⟨v, hvmem, hv⟩ := hmu.exists_hasEigenvector
  exact (hermitian_real_spectrum T hT mu v hv (by
    simpa [Module.End.mem_eigenspace_iff] using hvmem)).1

end QPhys

