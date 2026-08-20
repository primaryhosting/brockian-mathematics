/-
# Cos Trace Norm 1597
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1597
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cos Trace Norm 1597
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1597
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

/-- The "cosine trace" of the regular representation at angle `x`:
`∑_{k < n} cos (k * x)`. -/

theorem abs_cosTrace_le (n : ℕ) (x : ℝ) : |cosTrace n x| ≤ n := by
  calc |cosTrace n x| ≤ ∑ k ∈ Finset.range n, |Real.cos (k * x)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range n, (1 : ℝ) :=
        Finset.sum_le_sum fun k _ => Real.abs_cos_le_one _
    _ = n := by simp

/-- The bound is attained at `x = 0`. -/
