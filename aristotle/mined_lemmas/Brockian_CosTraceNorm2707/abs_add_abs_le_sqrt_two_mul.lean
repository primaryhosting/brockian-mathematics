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

/-- The larger eigenvalue of the real symmetric matrix `!![a, b; b, d]`. -/

theorem abs_add_abs_le_sqrt_two_mul (x y : ℝ) :
    |x| + |y| ≤ Real.sqrt 2 * Real.sqrt (x ^ 2 + y ^ 2) := by
  have hnn : (0:ℝ) ≤ x ^ 2 + y ^ 2 := by positivity
  have h1 : Real.sqrt 2 * Real.sqrt (x ^ 2 + y ^ 2) = Real.sqrt (2 * (x ^ 2 + y ^ 2)) :=
    (Real.sqrt_mul (by norm_num) _).symm
  rw [h1]
  have h2 : (|x| + |y|) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
    have := sq_nonneg (|x| - |y|)
    have hx : |x| ^ 2 = x ^ 2 := sq_abs x
    have hy : |y| ^ 2 = y ^ 2 := sq_abs y
    nlinarith
  have h3 : |x| + |y| = Real.sqrt ((|x| + |y|) ^ 2) :=
    (Real.sqrt_sq (by positivity)).symm
  rw [h3]
  exact Real.sqrt_le_sqrt h2

/-- **Cos Trace Norm 2707.**  For real symmetric `2 × 2` matrices `!![a, b; b, d]`, the trace
norm dominates the absolute trace, is dominated by `√2` times the Frobenius norm, and on the
cosine family `!![r cos θ, r sin θ; r sin θ, -r cos θ]` (`r ≥ 0`) it equals exactly `2r`, so
that both bounds are attained in the sharpest possible way (the trace vanishes while the
Frobenius bound `√2 · √(2 r²) = 2r` is an equality). -/
