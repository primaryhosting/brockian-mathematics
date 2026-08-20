import Mathlib

/-!
# Cos Trace Norm 3499
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3499
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix
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

namespace Brockian

/-- The trace norm (Schatten 1-norm, i.e. the sum of the singular values) of a square
matrix `A`, defined as `tr √(Aᴴ * A)`. -/

theorem cosMatrix_eq_gram {n : ℕ} (θ : Fin n → ℝ) :
    cosMatrix θ = (cosSinMatrix θ)ᴴ * cosSinMatrix θ := by
  ext i j
  simp [cosMatrix, cosSinMatrix, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_sub, mul_comm]

/-- The cosine kernel matrix is positive semidefinite. -/
