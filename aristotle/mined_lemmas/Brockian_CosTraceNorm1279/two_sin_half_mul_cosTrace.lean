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

lemma two_sin_half_mul_cosTrace (n : ℕ) (x : ℝ) :
    2 * Real.sin (x / 2) * cosTrace n x
      = Real.sin ((2 * (n : ℝ) - 1) * x / 2) + Real.sin (x / 2) := by
  induction n with
  | zero =>
      have h : (2 * ((0 : ℕ) : ℝ) - 1) * x / 2 = -(x / 2) := by push_cast; ring
      rw [h]
      simp
  | succ n ih =>
      have h1 : (2 * ((n + 1 : ℕ) : ℝ) - 1) * x / 2 = (n : ℝ) * x + x / 2 := by
        push_cast; ring
      have h2 : (2 * (n : ℝ) - 1) * x / 2 = (n : ℝ) * x - x / 2 := by ring
      rw [cosTrace_succ, h1]
      rw [h2] at ih
      rw [Real.sin_add]
      nlinarith [ih, Real.sin_sub ((n : ℝ) * x) (x / 2)]

/-- Trivial bound: the `cos`-trace of `n` terms has absolute value at most `n`. -/
