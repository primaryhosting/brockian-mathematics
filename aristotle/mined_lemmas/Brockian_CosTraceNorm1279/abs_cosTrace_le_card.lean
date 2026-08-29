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

/-- The `cos`-trace: the trace of the `n`-th truncated rotation family,
`∑_{k < n} cos (k x)`. -/

lemma abs_cosTrace_le_card (n : ℕ) (x : ℝ) : |cosTrace n x| ≤ (n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [cosTrace_succ]
      have h := abs_add_le (cosTrace n x) (Real.cos ((n : ℝ) * x))
      have hc : |Real.cos ((n : ℝ) * x)| ≤ 1 := Real.abs_cos_le_one _
      push_cast
      linarith

/-- Dirichlet bound: away from the zeros of `sin (x/2)`, the `cos`-trace is bounded
independently of `n`. -/
