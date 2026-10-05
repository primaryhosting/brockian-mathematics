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

namespace QPhys

open Matrix

/-- **Spectral theorem (finite dimensions).**

Every Hermitian matrix `A` (an observable in finite-dimensional quantum mechanics) is unitarily
diagonalizable with real eigenvalues: there exist a unitary matrix `U` and a *real*-valued
family of eigenvalues `d : n → ℝ` such that

* `U` is unitary (`Uᴴ * U = 1` and `U * Uᴴ = 1`),
* `A = U * diagonal d * Uᴴ`, equivalently `Uᴴ * A * U = diagonal d`,
* the `i`-th column of `U` is an eigenvector of `A` with eigenvalue `d i`,
* the spectrum of `A` is exactly the set of the (real) numbers `d i`.
-/
theorem spectral_theorem_finite {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    ∃ (U : Matrix n n ℂ) (d : n → ℝ),
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      A = U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ ∧
      Uᴴ * A * U = Matrix.diagonal (fun i => (d i : ℂ)) ∧
      (∀ i, A *ᵥ (fun k => U k i) = (d i : ℂ) • (fun k => U k i)) ∧
      (∀ z : ℂ, z ∈ spectrum ℂ A ↔ ∃ i, z = (d i : ℂ)) := by
  refine ⟨(hA.eigenvectorUnitary : Matrix n n ℂ), hA.eigenvalues, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Unitary.coe_star_mul_self _
  · exact Unitary.coe_mul_star_self _
  · conv_lhs => rw [hA.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply, Function.comp_def, Matrix.star_eq_conjTranspose]
  · have h := hA.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_apply] at h
    simpa [Matrix.star_eq_conjTranspose, Function.comp_def, mul_assoc] using h
  · intro i
    have h := hA.mulVec_eigenvectorBasis i
    have hcol : (fun k => (hA.eigenvectorUnitary : Matrix n n ℂ) k i)
        = ⇑(hA.eigenvectorBasis i) := rfl
    rw [hcol, h, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  · intro z
    rw [hA.spectrum_eq_image_range]
    simp [eq_comm]

end QPhys

