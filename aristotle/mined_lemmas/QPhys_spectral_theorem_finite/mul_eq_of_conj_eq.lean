/-
/-!
# Spectral Theorem Finite
Category: Quantum Physics
Target: QPhys.spectral_theorem_finite
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

namespace QPhys

open Matrix

/-- If `A = U * D * Uᴴ` with `U` unitary, then `A * U = U * D`. -/

private theorem mul_eq_of_conj_eq {n : Type*} [Fintype n] [DecidableEq n]
    (A U D : Matrix n n ℂ) (hU : U ∈ Matrix.unitaryGroup n ℂ) (h : A = U * D * Uᴴ) :
    A * U = U * D := by
  have h1 : Uᴴ * U = 1 := hU.1
  rw [h, mul_assoc, mul_assoc, h1, mul_one]

/-- **Spectral theorem (finite dimensions).**
Every Hermitian matrix `A` over `ℂ` is unitarily diagonalizable with *real* eigenvalues:
there are a unitary matrix `U` and a real-valued family `d` such that
`A = U * diagonal d * Uᴴ`, equivalently `A * U = U * diagonal d`, so that the `i`-th column
of `U` is an eigenvector of `A` with real eigenvalue `d i`.

The core input is Mathlib's `Matrix.IsHermitian.spectral_theorem`. -/
