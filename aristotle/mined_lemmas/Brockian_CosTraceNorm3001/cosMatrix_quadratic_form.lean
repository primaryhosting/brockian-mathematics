/-
# Cos Trace Norm 3001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3001
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

open Matrix

/-- The "cosine kernel" matrix attached to a family of angles `θ : Fin n → ℝ`:
its `(i, j)` entry is `cos (θ i - θ j)`. -/

lemma cosMatrix_quadratic_form (n : ℕ) (θ : Fin n → ℝ) (x : Fin n → ℝ) :
    star x ⬝ᵥ (cosMatrix n θ *ᵥ x)
      = (∑ i, x i * Real.cos (θ i)) ^ 2 + (∑ i, x i * Real.sin (θ i)) ^ 2 := by
  have h1 : ((∑ i, x i * Real.cos (θ i)) ^ 2 : ℝ)
      = ∑ i, ∑ j, (x i * Real.cos (θ i)) * (x j * Real.cos (θ j)) := by
    rw [sq, Finset.sum_mul_sum]
  have h2 : ((∑ i, x i * Real.sin (θ i)) ^ 2 : ℝ)
      = ∑ i, ∑ j, (x i * Real.sin (θ i)) * (x j * Real.sin (θ j)) := by
    rw [sq, Finset.sum_mul_sum]
  rw [h1, h2, ← Finset.sum_add_distrib]
  simp only [dotProduct, Matrix.mulVec, cosMatrix, Matrix.of_apply, Pi.star_apply,
    star_trivial, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Real.cos_sub]
  ring

/-- The cosine kernel matrix is positive semidefinite. -/
