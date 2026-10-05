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

noncomputable def ptrace (psi : Fin n × Fin m → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => ∑ k, psi (i, k) * (starRingEnd ℂ) (psi (j, k))

