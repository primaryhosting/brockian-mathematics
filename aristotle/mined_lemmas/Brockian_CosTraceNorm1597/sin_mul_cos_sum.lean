/-
# Cos Trace Norm 1597
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1597
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

/-- The `n × n` real "cosine Hankel" matrix with entries `cos (θ * (i + j))`. -/

lemma sin_mul_cos_sum (θ : ℝ) (n : ℕ) :
    Real.sin θ * ∑ k ∈ Finset.range n, Real.cos (2 * θ * k)
      = (Real.sin ((2 * n - 1) * θ) + Real.sin θ) / 2 := by
  induction n with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, mul_zero, Nat.cast_zero]
      rw [show (((0 : ℝ) - 1) * θ) = -θ by ring, Real.sin_neg]
      ring
  | succ m ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      have h1 : ((2 * (m + 1 : ℕ) : ℝ) - 1) * θ = 2 * m * θ + θ := by
        push_cast; ring
      have h2 : ((2 * (m : ℕ) : ℝ) - 1) * θ = 2 * m * θ - θ := by ring
      rw [h1, h2, Real.sin_add, Real.sin_sub]
      have : Real.sin θ * Real.cos (2 * θ * m) = Real.sin θ * Real.cos (2 * m * θ) := by
        ring_nf
      rw [this]
      ring

/-- Trivial bound: the cosine sum is bounded by the number of terms. -/
