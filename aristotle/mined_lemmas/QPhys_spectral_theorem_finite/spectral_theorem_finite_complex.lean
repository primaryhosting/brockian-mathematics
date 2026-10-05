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

theorem spectral_theorem_finite_complex {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    ∃ (U : Matrix n n ℂ) (d : n → ℝ),
      (star U * U = 1 ∧ U * star U = 1) ∧
      A = U * Matrix.diagonal (fun i => (d i : ℂ)) * star U ∧
      (∀ i, A *ᵥ (fun j => U j i) = (d i : ℂ) • (fun j => U j i)) ∧
      (∀ i, (d i : ℂ) ∈ spectrum ℂ A) :=
  spectral_theorem_finite A hA

end QPhys

