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
open scoped Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace QPhys

/-- **Finite-dimensional spectral theorem.**
Every Hermitian matrix `A` over `ℂ` (indexed by a finite type `n`) is unitarily
diagonalizable with *real* eigenvalues: there is a unitary matrix `U`
(`Uᴴ * U = 1` and `U * Uᴴ = 1`) and a real-valued function `d : n → ℝ` with

* `A = U * diagonal (fun i => (d i : ℂ)) * Uᴴ`,
* each `d i` is an eigenvalue of `A`, with the `i`-th column of `U` as an
  eigenvector, and
* the spectrum of `A` is exactly the (real) set of values of `d`. -/

theorem spectral_theorem_finite {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    ∃ (U : Matrix n n ℂ) (d : n → ℝ),
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      A = U * Matrix.diagonal (fun i => ((d i : ℝ) : ℂ)) * Uᴴ ∧
      (∀ i, A *ᵥ (fun j => U j i) = ((d i : ℝ) : ℂ) • (fun j => U j i)) ∧
      spectrum ℂ A = (fun r : ℝ => (r : ℂ)) '' Set.range d := by
  classical
  refine ⟨(hA.eigenvectorUnitary : Matrix n n ℂ), hA.eigenvalues, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Matrix.star_eq_conjTranspose] using
      (Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2)
  · simpa [Matrix.star_eq_conjTranspose] using
      (Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2)
  · have := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    simpa [Matrix.star_eq_conjTranspose, Function.comp_def, mul_assoc] using this
  · intro i
    have hcol : Matrix.col (hA.eigenvectorUnitary : Matrix n n ℂ) i
        = ⇑(hA.eigenvectorBasis i) := Matrix.IsHermitian.eigenvectorUnitary_col_eq hA i
    have h := hA.mulVec_eigenvectorBasis i
    have hfun : (fun j => (hA.eigenvectorUnitary : Matrix n n ℂ) j i)
        = ⇑(hA.eigenvectorBasis i) := hcol
    rw [hfun, h]
    ext j
    simp [Complex.real_smul]
  · have := hA.spectrum_eq_image_range
    simpa using this

end QPhys

