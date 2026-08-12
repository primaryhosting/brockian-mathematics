import Mathlib

/-!
# Exceeds Bound At 5040
Category: Riemann Program
Target: Riemann.Robin.exceeds_bound_at_5040
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

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Riemann.Robin

/-- For all real `E, LL` with `0 ≤ E ≤ 1.782` and `0 ≤ LL ≤ 2.143`, we have
`E * 5040 * LL < 19344`.  Combined with `σ(5040) = 19344`, `e^γ ≤ 1.782` and
`log (log 5040) ≤ 2.143`, this shows Robin's bound `e^γ * n * log log n` is
exceeded by `σ(n)` at `n = 5040`.

The hypothesis `0 ≤ E` is kept because it is part of the requested statement,
although the proof does not need it. -/
theorem exceeds_bound_at_5040 (E LL : ℝ) (hE0 : 0 ≤ E) (hE : E ≤ 1.782)
    (hL0 : 0 ≤ LL) (hL : LL ≤ 2.143) : E * 5040 * LL < 19344 := by
  have hE5 : E * 5040 ≤ 1.782 * 5040 := by linarith
  have h := mul_le_mul hE5 hL hL0 (by norm_num : (0:ℝ) ≤ 1.782 * 5040)
  linarith

end Riemann.Robin

