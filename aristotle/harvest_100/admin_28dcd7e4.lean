/-
# Spectral Theorem Finite
Category: Quantum Physics
Target: QPhys.spectral_theorem_finite
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Spectral Theorem Finite
Category: Quantum Physics
Target: QPhys.spectral_theorem_finite
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

open Matrix

namespace QPhys

/-- **Spectral theorem for finite-dimensional Hermitian (self-adjoint) matrices.**

Every Hermitian matrix `A` over an `RCLike` field `𝕜` (in particular over `ℂ`, the case
relevant for quantum mechanics) is unitarily diagonalizable with *real* eigenvalues:
there exist a unitary matrix `U` (`star U * U = 1` and `U * star U = 1`) and a function
`d : n → ℝ` such that

* `A = U * diagonal (fun i => (d i : 𝕜)) * star U`,
* each column of `U` is an eigenvector of `A` with eigenvalue `d i`,
* each `d i` belongs to the spectrum of `A`. -/
theorem spectral_theorem_finite {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n 𝕜) (hA : A.IsHermitian) :
    ∃ (U : Matrix n n 𝕜) (d : n → ℝ),
      (star U * U = 1 ∧ U * star U = 1) ∧
      A = U * Matrix.diagonal (fun i => (d i : 𝕜)) * star U ∧
      (∀ i, A *ᵥ (fun j => U j i) = (d i : 𝕜) • (fun j => U j i)) ∧
      (∀ i, (d i : 𝕜) ∈ spectrum 𝕜 A) := by
  classical
  refine ⟨(hA.eigenvectorUnitary : Matrix n n 𝕜), hA.eigenvalues, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · exact Unitary.coe_star_mul_self hA.eigenvectorUnitary
  · exact Unitary.coe_mul_star_self hA.eigenvectorUnitary
  · conv_lhs => rw [hA.spectral_theorem]
    rfl
  · intro i
    have h := hA.mulVec_eigenvectorBasis i
    have hcol : (fun j => (hA.eigenvectorUnitary : Matrix n n 𝕜) j i)
        = ⇑(hA.eigenvectorBasis i) := rfl
    rw [hcol, h, RCLike.real_smul_eq_coe_smul (K := 𝕜)]
  · intro i
    rw [hA.spectrum_eq_image_range]
    exact ⟨hA.eigenvalues i, Set.mem_range_self i, rfl⟩

/-- Specialization of the spectral theorem to complex Hermitian matrices, the standard setting
for observables in quantum mechanics. -/
theorem spectral_theorem_finite_complex {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    ∃ (U : Matrix n n ℂ) (d : n → ℝ),
      (star U * U = 1 ∧ U * star U = 1) ∧
      A = U * Matrix.diagonal (fun i => (d i : ℂ)) * star U ∧
      (∀ i, A *ᵥ (fun j => U j i) = (d i : ℂ) • (fun j => U j i)) ∧
      (∀ i, (d i : ℂ) ∈ spectrum ℂ A) :=
  spectral_theorem_finite A hA

end QPhys

