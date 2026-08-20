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

lemma abs_cos_sum_le_card (θ : ℝ) (n : ℕ) :
    |∑ k ∈ Finset.range n, Real.cos (2 * θ * k)| ≤ n := by
  calc |∑ k ∈ Finset.range n, Real.cos (2 * θ * k)|
      ≤ ∑ k ∈ Finset.range n, |Real.cos (2 * θ * k)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range n, (1 : ℝ) := by
        refine Finset.sum_le_sum ?_
        intro k _
        exact Real.abs_cos_le_one _
    _ = n := by simp

/-- Dirichlet-type bound: away from the zeros of `sin`, the cosine sum is bounded by
`1 / |sin θ|`, uniformly in the number of terms. -/
