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

/-
# Exceeds Bound At 5040
Category: Riemann Program
Target: Riemann.Robin.exceeds_bound_at_5040
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Riemann.Robin

/-- For all real `E, LL` with `0 ≤ E ≤ 1.782` and `0 ≤ LL ≤ 2.143`, we have
`E * 5040 * LL < 19344`.

Combined with `σ(5040) = 19344`, `e^γ ≤ 1.782` and `log (log 5040) ≤ 2.143`,
this shows that Robin's bound `e^γ * n * log log n` is exceeded by `σ(n)` at `n = 5040`.

The hypothesis `0 ≤ E` is kept because it is part of the requested statement, but the proof
does not need it: the bound already follows from `E ≤ 1.782`, `0 ≤ LL` and `LL ≤ 2.143`. -/
theorem exceeds_bound_at_5040 (E LL : ℝ) (hE0 : 0 ≤ E) (hE : E ≤ 1.782)
    (hLL0 : 0 ≤ LL) (hLL : LL ≤ 2.143) :
    E * 5040 * LL < 19344 := by
  have h1 : E * 5040 * LL ≤ 1.782 * 5040 * LL := by nlinarith [hLL0]
  have h2 : 1.782 * 5040 * LL ≤ 1.782 * 5040 * 2.143 := by nlinarith
  linarith

end Riemann.Robin

