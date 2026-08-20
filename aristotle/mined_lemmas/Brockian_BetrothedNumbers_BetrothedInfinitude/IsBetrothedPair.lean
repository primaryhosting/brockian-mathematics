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
# Betrothed Infinitude
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.BetrothedInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain block comment rather than a `/-!` module docstring:
-- Lean 4 requires `import` commands to precede every other command, including module
-- docstrings.  The same text is repeated as the module docstring after the import.)

import Mathlib

/-!
# Betrothed Infinitude
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.BetrothedInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 40000

set_option maxHeartbeats 2000000

namespace Brockian.BetrothedNumbers

open Finset

/-- The classical divisor sum `σ₁ n = ∑_{d ∣ n} d`. -/

theorem IsBetrothedPair.odd_add_of_not_two_pow_mul_sq {m n : ℕ} (h : IsBetrothedPair m n)
    (hm : ¬ ∃ a k : ℕ, 0 < k ∧ m = 2 ^ a * k ^ 2) : Odd (m + n) := by
  rcases Nat.even_or_odd (m + n) with he | ho
  · exact absurd (h.two_pow_mul_sq_of_even_add he).1 hm
  · exact ho

/-! ## The conditional infinitude statement -/

/-- **Betrothed Infinitude (conditional reduction).**

Whether infinitely many betrothed (quasi-amicable) pairs exist is an open problem, so the
statement is proved here as a reduction: the two-variable infinitude assertion follows from
the *one-variable* condition that arbitrarily large `m` satisfy `IsBetrothed m`, i.e.
`n := σ₁(m) - m - 1` is a positive number different from `m` with `σ₁(n) = σ₁(m)`. -/
