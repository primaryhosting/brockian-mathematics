import Mathlib

/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder
open Matrix

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

namespace QI

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The amplification `id_p ⊗ Φ` of a linear map `Φ` between matrix algebras:
a `(p × n)`-matrix is viewed as a `p × p` block matrix of `n × n` blocks, and `Φ`
is applied to each block. -/

def amplify (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) (p : Type) [Fintype p]
    (A : Matrix (p × n) (p × n) ℂ) : Matrix (p × m) (p × m) ℂ :=
  Matrix.of fun x y => Φ (Matrix.of fun i j => A (x.1, i) (y.1, j)) x.2 y.2

/-- `Φ` is completely positive when all its amplifications `id_p ⊗ Φ` map positive
semidefinite matrices to positive semidefinite matrices. -/
