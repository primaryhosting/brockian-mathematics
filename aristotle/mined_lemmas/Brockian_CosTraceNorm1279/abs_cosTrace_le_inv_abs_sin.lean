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

lemma abs_cosTrace_le_inv_abs_sin (n : ℕ) (x : ℝ) (hx : Real.sin (x / 2) ≠ 0) :
    |cosTrace n x| ≤ 1 / |Real.sin (x / 2)| := by
  have key := two_sin_half_mul_cosTrace n x
  have h1 : |2 * Real.sin (x / 2) * cosTrace n x| ≤ 2 := by
    rw [key]
    calc |Real.sin ((2 * (n : ℝ) - 1) * x / 2) + Real.sin (x / 2)|
        ≤ |Real.sin ((2 * (n : ℝ) - 1) * x / 2)| + |Real.sin (x / 2)| := abs_add_le _ _
      _ ≤ 1 + 1 := by
          have := Real.abs_sin_le_one ((2 * (n : ℝ) - 1) * x / 2)
          have := Real.abs_sin_le_one (x / 2)
          linarith
      _ = 2 := by norm_num
  have habs : (0 : ℝ) < |Real.sin (x / 2)| := abs_pos.mpr hx
  rw [abs_mul, abs_mul, abs_two] at h1
  rw [le_div_iff₀ habs]
  nlinarith [h1, habs]

/-- **Cos Trace Norm 1279.**  For every `n` and every real `x`, the truncated
`cos`-trace `∑_{k < n} cos (k x)` satisfies both the trivial norm bound `n`
and, away from the zeros of `sin (x/2)`, the uniform Dirichlet bound
`1 / |sin (x/2)|`. -/
