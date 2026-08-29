import Mathlib
/-!
# Hermitian Real Spectrum
Category: Quantum Physics
Target: QPhys.hermitian_real_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

open scoped InnerProductSpace ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Every eigenvalue of a Hermitian operator is real.**

If `T` is a Hermitian (symmetric / self-adjoint) linear operator on a complex inner product
space and `T v = μ • v` for some nonzero vector `v`, then the eigenvalue `μ` is a real number. -/
theorem hermitian_real_spectrum
    (T : E →ₗ[ℂ] E) (hT : ∀ x y : E, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ)
    (μ : ℂ) (v : E) (hv : v ≠ 0) (heig : T v = μ • v) :
    ∃ r : ℝ, μ = (r : ℂ) := by
  have hnorm : (⟪v, v⟫_ℂ) ≠ 0 := by
    simpa [inner_self_eq_zero] using hv
  have key : conj μ * ⟪v, v⟫_ℂ = μ * ⟪v, v⟫_ℂ := by
    have h1 : ⟪T v, v⟫_ℂ = conj μ * ⟪v, v⟫_ℂ := by
      rw [heig, inner_smul_left]
    have h2 : ⟪v, T v⟫_ℂ = μ * ⟪v, v⟫_ℂ := by
      rw [heig, inner_smul_right]
    rw [← h1, ← h2]
    exact hT v v
  have hμ : conj μ = μ := mul_right_cancel₀ hnorm key
  exact ⟨μ.re, (Complex.conj_eq_iff_re.mp hμ).symm⟩

/-- Reformulation: an eigenvalue of a Hermitian operator equals its own complex conjugate. -/
theorem hermitian_eigenvalue_conj_eq_self
    (T : E →ₗ[ℂ] E) (hT : ∀ x y : E, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ)
    (μ : ℂ) (v : E) (hv : v ≠ 0) (heig : T v = μ • v) :
    conj μ = μ := by
  obtain ⟨r, hr⟩ := hermitian_real_spectrum T hT μ v hv heig
  simp [hr]

/-- Matrix corollary: every eigenvalue of a Hermitian matrix is real. -/
theorem hermitian_matrix_real_spectrum {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) (μ : ℂ) (v : n → ℂ) (hv : v ≠ 0)
    (heig : A.mulVec v = μ • v) :
    ∃ r : ℝ, μ = (r : ℂ) := by
  have hsym := Matrix.isHermitian_iff_isSymmetric.mp hA
  refine hermitian_real_spectrum (E := EuclideanSpace ℂ n) (Matrix.toEuclideanLin A)
    (fun x y => hsym x y) μ (WithLp.toLp 2 v) ?_ ?_
  · simpa using hv
  · ext i
    simp [heig]

end QPhys

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

