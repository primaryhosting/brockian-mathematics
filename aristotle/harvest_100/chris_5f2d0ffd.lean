import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QPhys

/-- If `A = U * diagonal d * Uᴴ` with `Uᴴ * U = 1`, then the `i`-th column of `U` is an
eigenvector of `A` with eigenvalue `d i`. -/
private theorem col_isEigenvector_of_diagonalization {n : Type*} [Fintype n] [DecidableEq n]
    (A U : Matrix n n ℂ) (d : n → ℝ) (hU : Uᴴ * U = 1)
    (h : A = U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ) (i : n) :
    A *ᵥ (fun k => U k i) = (d i : ℂ) • (fun k => U k i) := by
  classical
  have hAU : A * U = U * Matrix.diagonal (fun i => (d i : ℂ)) := by
    conv_lhs => rw [h]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hU, Matrix.mul_one]
  funext k
  have := congrArg (fun M : Matrix n n ℂ => M k i) hAU
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.diagonal, Finset.sum_ite_eq',
    mul_comm] using this

/-- **Finite-dimensional spectral theorem.**

Every Hermitian matrix `A` over `ℂ` (indexed by a finite type `n`) is unitarily
diagonalizable with real eigenvalues: there is a unitary matrix `U` and a real-valued
function `d : n → ℝ` such that

* `Uᴴ * A * U` is the diagonal matrix with entries `d i` (all real);
* equivalently `A = U * diagonal d * Uᴴ`;
* the `i`-th column of `U` is an eigenvector of `A` with eigenvalue `d i`;
* the spectrum of `A` is exactly the (real) set of values of `d`.
-/
theorem spectral_theorem_finite {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    ∃ (U : Matrix n n ℂ) (d : n → ℝ),
      U ∈ Matrix.unitaryGroup n ℂ ∧
      Uᴴ * A * U = Matrix.diagonal (fun i => (d i : ℂ)) ∧
      A = U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ ∧
      (∀ i : n, A *ᵥ (fun k => U k i) = (d i : ℂ) • (fun k => U k i)) ∧
      spectrum ℂ A = (fun r : ℝ => (r : ℂ)) '' Set.range d := by
  classical
  refine ⟨(hA.eigenvectorUnitary : Matrix n n ℂ), hA.eigenvalues,
    (hA.eigenvectorUnitary).2, ?_, ?_, ?_, ?_⟩
  · have h := hA.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at h
    simpa [Matrix.star_eq_conjTranspose, Function.comp_def] using h
  · have h := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    simpa [Matrix.star_eq_conjTranspose, Function.comp_def] using h
  · have h : A = (hA.eigenvectorUnitary : Matrix n n ℂ) *
        Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) *
        (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
      have h := hA.spectral_theorem
      rw [Unitary.conjStarAlgAut_apply] at h
      simpa [Matrix.star_eq_conjTranspose, Function.comp_def] using h
    have hU : (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ *
        (hA.eigenvectorUnitary : Matrix n n ℂ) = 1 := by
      have := (hA.eigenvectorUnitary).2
      rw [Matrix.mem_unitaryGroup_iff'] at this
      simpa [Matrix.star_eq_conjTranspose] using this
    exact fun i => col_isEigenvector_of_diagonalization A _ _ hU h i
  · simpa [Function.comp_def] using hA.spectrum_eq_image_range

end QPhys

