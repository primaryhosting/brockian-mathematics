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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

open Matrix

universe u v

/-! ## Linear-algebraic preliminaries -/

/-- The inner product of two images under a matrix, expressed through `Mᴴ * M`. -/

theorem inner_toEuclideanLin_eq {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
    (M : Matrix m n ℂ) (x y : EuclideanSpace ℂ n) :
    inner ℂ (Matrix.toEuclideanLin M x) (Matrix.toEuclideanLin M y)
      = ((Mᴴ * M) *ᵥ y.ofLp) ⬝ᵥ star x.ofLp := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Matrix.toLpLin_apply, WithLp.ofLp_toLp]
  rw [star_mulVec, dotProduct_comm, ← dotProduct_mulVec, mulVec_mulVec, dotProduct_comm]

/-- The matrix of a linear isometry of a finite-dimensional Euclidean space is unitary. -/
