/-
# Exceeds Bound At 5040
Category: Riemann Program
Target: Riemann.Robin.exceeds_bound_at_5040
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Riemann.Robin

/-- For `0 ≤ E ≤ 1.782` and `0 ≤ LL ≤ 2.143` we have `E * 5040 * LL < 19344`.
Since `σ(5040) = 19344`, `e^γ ≤ 1.782` and `log (log 5040) ≤ 2.143`, this shows that
Robin's bound `e^γ * n * log log n` is exceeded by `σ(n)` at `n = 5040`.

(The hypothesis `0 ≤ E` is part of the requested statement; the proof does not need it.) -/
theorem exceeds_bound_at_5040 (E LL : ℝ) (hE0 : 0 ≤ E) (hE : E ≤ 1.782)
    (hL0 : 0 ≤ LL) (hL : LL ≤ 2.143) : E * 5040 * LL < 19344 := by
  nlinarith [mul_nonneg hE0 hL0, mul_le_mul hE hL hL0 (by norm_num : (0:ℝ) ≤ 1.782)]

end Riemann.Robin

