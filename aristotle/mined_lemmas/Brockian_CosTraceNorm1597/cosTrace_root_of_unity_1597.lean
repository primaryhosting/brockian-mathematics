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

theorem cosTrace_root_of_unity_1597 :
    (∑ k ∈ Finset.range 1597, Real.cos (2 * Real.pi * k / 1597)) = 0 := by
  have h := (Complex.isPrimitiveRoot_exp 1597 (by norm_num)).geom_sum_eq_zero (by norm_num)
  have h2 := congrArg Complex.re h
  rw [Complex.re_sum, Complex.zero_re] at h2
  rw [← h2]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [← Complex.exp_nat_mul]
  have hk : (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / ((1597 : ℕ) : ℂ)) =
      ((2 * Real.pi * k / 1597 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hk, Complex.exp_ofReal_mul_I_re]

/-- The cosine trace is bounded in absolute value by the dimension. -/
