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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

open Matrix

/-- The quadratic form of the cosine Gram matrix `cos (x i - x j)` is a sum of two squares. -/

lemma cos_gram_quadratic_form_le (n : ℕ) (x v : Fin n → ℝ) :
    ∑ i, ∑ j, v i * v j * Real.cos (x i - x j) ≤ (n : ℝ) * ∑ i, v i ^ 2 := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v (fun i => Real.cos (x i))
  have hs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v (fun i => Real.sin (x i))
  have hsum : (∑ i, Real.cos (x i) ^ 2) + (∑ i, Real.sin (x i) ^ 2) = (n : ℝ) := by
    rw [← Finset.sum_add_distrib]
    simp [Real.cos_sq_add_sin_sq]
  rw [cos_gram_quadratic_form n x v]
  calc (∑ i, v i * Real.cos (x i)) ^ 2 + (∑ i, v i * Real.sin (x i)) ^ 2
      ≤ (∑ i, v i ^ 2) * (∑ i, Real.cos (x i) ^ 2) + (∑ i, v i ^ 2) * (∑ i, Real.sin (x i) ^ 2) :=
        add_le_add hc hs
    _ = (n : ℝ) * ∑ i, v i ^ 2 := by rw [← mul_add, hsum]; ring

/-- **Cos Trace Norm 3001.**
For any phases `x : Fin n → ℝ`, the cosine Gram matrix `M i j = cos (x i - x j)` is positive
semidefinite, its trace norm (the sum of the absolute values of its eigenvalues) equals `n`,
and its quadratic form obeys the sharp bound `vᵀ M v ≤ n ‖v‖²`. -/
