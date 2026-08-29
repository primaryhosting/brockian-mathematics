/-
# Cos Trace Norm 3499
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3499
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.piBinderTypes true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true

set_option grind.warning false

namespace Brockian

/-- The `n × n` real "cosine Gram" matrix attached to a family of phases `x : Fin n → ℝ`,
with entries `cos (x i - x j)`. -/

lemma cosGram_eq_factor (n : ℕ) (x : Fin n → ℝ) :
    (cosFactor n x)ᴴ * cosFactor n x = cosGram n x := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, cosFactor, cosGram, Matrix.of_apply,
    star_trivial]
  rw [Fin.sum_univ_two]
  simp [Real.cos_sub]

/-- The cosine Gram matrix is positive semidefinite (it is a genuine Gram matrix). -/
