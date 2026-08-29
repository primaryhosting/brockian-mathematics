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

/-!
# Betrothed Infinitude
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.BetrothedInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.BetrothedNumbers

/-! ## Basic definitions

Everything below is developed from first principles (no imports), so that the
module docstring above can legally be the first thing in the file. -/

/-- The predicate selecting the positive divisors of `n`. -/

theorem betrothed_5775_6128 : Betrothed 5775 6128 :=
  ⟨by omega, by omega, by omega, sigmaSum_5775, sigmaSum_6128⟩

/-! ## The reduction -/

/-- **Betrothed Infinitude (conditional reduction).**
Assume no quasi-perfect number exists (`σ(k) ≠ 2k + 1` for all `k`; a classical
conjecture, verified far beyond every computed range).  Then there are infinitely
many betrothed (quasi-amicable) pairs if and only if the quasi-aliquot map
`s*(n) = σ(n) - n - 1` has infinitely many points lying on `2`-cycles. -/
