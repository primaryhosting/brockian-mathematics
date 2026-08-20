import Mathlib

/-!
# Cos Trace Norm 1279
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1279
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

/-- The cosine Gram matrix of a family of angles: `C i j = cos (θ i - θ j)`. -/

theorem cosGram_eq_conjTranspose_mul_self (n : ℕ) (θ : Fin n → ℝ) :
    cosGram n θ = (cosSinRows n θ).conjTranspose * (cosSinRows n θ) := by
  ext i j
  simp [cosGram, cosSinRows, Matrix.mul_apply,
    Fin.sum_univ_two, Real.cos_sub, mul_comm]

/-- Key intermediate lemma: the cosine Gram matrix is positive semidefinite. -/
