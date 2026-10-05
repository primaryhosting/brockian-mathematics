/-
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option maxHeartbeats 1000000

open scoped MatrixOrder ComplexOrder Kronecker InnerProductSpace
open Matrix

namespace QI

variable {n m : ℕ}

/-- The coefficient matrix of a vector `psi` of the tensor product `ℂ^n ⊗ ℂ^m`, whose
coordinates are indexed by `Fin n × Fin m`. -/

lemma ptrace_eq_mul_conjTranspose (psi : Fin n × Fin m → ℂ) :
    ptrace psi = coeffMatrix psi * (coeffMatrix psi)ᴴ := by
  ext i j
  simp [ptrace, coeffMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- If two `n × m` matrices have the same Gram matrix `A * Aᴴ`, then they differ by a
unitary matrix acting on the right. -/
