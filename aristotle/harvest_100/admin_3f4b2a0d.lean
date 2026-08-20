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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false


namespace Riemann.Robin

/-- For all real `E, LL` with `0 ≤ E ≤ 1.782` and `0 ≤ LL ≤ 2.143`, we have
`E * 5040 * LL < 19344`.  Combined with `σ(5040) = 19344`, `e^γ ≤ 1.782` and
`log (log 5040) ≤ 2.143`, this shows Robin's bound `e^γ * n * log log n` is
exceeded by `σ(n)` at `n = 5040`.

The hypothesis `0 ≤ LL` is part of the requested statement but is not needed for
the proof (the bound follows from `0 ≤ E`, `E ≤ 1.782` and `LL ≤ 2.143` alone). -/
theorem exceeds_bound_at_5040 (E LL : ℝ) (hE0 : 0 ≤ E) (hE : E ≤ 1.782)
    (hLL0 : 0 ≤ LL) (hLL : LL ≤ 2.143) : E * 5040 * LL < 19344 := by
  nlinarith [mul_nonneg hE0 hLL0, hE0, hLL0]

end Riemann.Robin

#print axioms Riemann.Robin.exceeds_bound_at_5040

