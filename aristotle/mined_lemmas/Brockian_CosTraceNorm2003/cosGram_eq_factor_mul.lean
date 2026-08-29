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
# Cos Trace Norm 2003
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2003
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Brockian

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace norm (Schatten 1-norm) of a Hermitian real matrix, defined as the sum of the
absolute values of its eigenvalues (and `0` on non-Hermitian matrices). -/

theorem cosGram_eq_factor_mul (w θ : n → ℝ) :
    cosGram w θ = cosFactor w θ * (cosFactor w θ).conjTranspose := by
  ext i j
  simp only [cosGram, cosFactor, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    star_trivial]
  rw [Fin.sum_univ_two]
  simp only [Real.cos_sub]
  norm_num
  ring

omit [DecidableEq n] in
/-- The weighted cosine Gram matrix is positive semidefinite. -/
