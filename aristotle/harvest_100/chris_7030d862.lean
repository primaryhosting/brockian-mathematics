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

import Mathlib

/-!
# Spectral Theorem Finite
Category: Quantum Physics
Target: QPhys.spectral_theorem_finite
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Matrix

namespace QPhys

/-- **Spectral theorem for Hermitian matrices (finite dimensions).**

Every Hermitian matrix `A` over `ℂ` (indexed by a finite type `n`) is unitarily
diagonalizable with real eigenvalues: there is a unitary matrix `U` and a real-valued
function `d : n → ℝ` such that

* `Uᴴ * U = 1` and `U * Uᴴ = 1` (i.e. `U` is unitary),
* `A = U * diagonal (fun i => (d i : ℂ)) * Uᴴ`,
* equivalently `Uᴴ * A * U = diagonal (fun i => (d i : ℂ))`,
* each `d i` is a (real) eigenvalue of `A`, i.e. `(d i : ℂ) ∈ spectrum ℂ A`.
-/
theorem spectral_theorem_finite {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    ∃ (U : Matrix n n ℂ) (d : n → ℝ),
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      A = U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ ∧
      Uᴴ * A * U = Matrix.diagonal (fun i => (d i : ℂ)) ∧
      ∀ i, ((d i : ℂ)) ∈ spectrum ℂ A := by
  classical
  refine ⟨(hA.eigenvectorUnitary : Matrix n n ℂ), hA.eigenvalues, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Matrix.star_eq_conjTranspose] using
      Unitary.coe_star_mul_self (hA.eigenvectorUnitary)
  · simpa [Matrix.star_eq_conjTranspose] using
      Unitary.coe_mul_star_self (hA.eigenvectorUnitary)
  · have := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    simpa [Matrix.star_eq_conjTranspose, Function.comp_def] using this
  · have := hA.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_apply] at this
    simpa [Matrix.star_eq_conjTranspose, Function.comp_def] using this
  · intro i
    have h : hA.eigenvalues i ∈ spectrum ℝ A := hA.eigenvalues_mem_spectrum_real i
    rw [← spectrum.preimage_algebraMap ℂ] at h
    simpa using h

end QPhys

