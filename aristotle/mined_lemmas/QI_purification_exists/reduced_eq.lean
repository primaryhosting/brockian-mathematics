/-
/-!
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to be the first command, so the mandated header above is kept as a
-- plain comment and repeated as the module docstring below.)
-/

import Mathlib

/-!
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder
open scoped MatrixOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Matrix

section Defs

variable {n m : Type*}

/-- The matrix `n × m` representation of a vector `ψ` of the tensor product `H ⊗ K`,
where `H` has orthonormal basis indexed by `n` and `K` has orthonormal basis indexed by `m`. -/

theorem reduced_eq [Fintype m] (psi : n × m → ℂ) :
    reduced psi = toMat psi * (toMat psi)ᴴ := by
  ext i j
  simp [reduced, toMat, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- The squared norm of the vector `ψ` equals the trace of the corresponding reduced state. -/
