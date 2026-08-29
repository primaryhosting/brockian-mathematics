/-
# Cos Trace Norm 2707
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2707
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian

/-- The quadratic form of the cosine kernel `cos (θ i - θ j)` is a sum of two squares. -/

theorem cos_kernel_posSemidef {ι : Type*} [Fintype ι] (θ : ι → ℝ) :
    (Matrix.of (fun i j : ι => Real.cos (θ i - θ j))).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext i j
    simp [Matrix.conjTranspose, ← Real.cos_neg (θ i - θ j)]
  · intro x
    refine le_of_le_of_eq (cos_kernel_nonneg θ x) ?_
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, mul_comm]

/-- The trace norm (sum of the absolute values of the eigenvalues, equivalently the sum of the
singular values) of the cosine kernel matrix equals `card ι`. -/
