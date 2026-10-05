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

theorem cos_kernel_le_card_mul {ι : Type*} [Fintype ι] (θ x : ι → ℝ) :
    ∑ i, ∑ j, x i * x j * Real.cos (θ i - θ j)
      ≤ (Fintype.card ι : ℝ) * ∑ i, x i ^ 2 := by
  rw [cos_kernel_quadratic_form]
  have hc : (∑ i, x i * Real.cos (θ i)) ^ 2
      ≤ (∑ i, x i ^ 2) * ∑ i, Real.cos (θ i) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hs : (∑ i, x i * Real.sin (θ i)) ^ 2
      ≤ (∑ i, x i ^ 2) * ∑ i, Real.sin (θ i) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hsum : (∑ i, Real.cos (θ i) ^ 2) + ∑ i, Real.sin (θ i) ^ 2
      = (Fintype.card ι : ℝ) := by
    rw [← Finset.sum_add_distrib]
    simp [Real.cos_sq_add_sin_sq, Finset.card_univ]
  calc (∑ i, x i * Real.cos (θ i)) ^ 2 + (∑ i, x i * Real.sin (θ i)) ^ 2
      ≤ (∑ i, x i ^ 2) * (∑ i, Real.cos (θ i) ^ 2)
        + (∑ i, x i ^ 2) * ∑ i, Real.sin (θ i) ^ 2 := add_le_add hc hs
    _ = (∑ i, x i ^ 2) * ((∑ i, Real.cos (θ i) ^ 2) + ∑ i, Real.sin (θ i) ^ 2) := by ring
    _ = (Fintype.card ι : ℝ) * ∑ i, x i ^ 2 := by rw [hsum]; ring

/-- The cosine kernel matrix is positive semidefinite in the sense of `Matrix.PosSemidef`. -/
