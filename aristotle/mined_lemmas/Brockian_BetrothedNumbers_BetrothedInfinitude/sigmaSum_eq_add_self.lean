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

theorem sigmaSum_eq_add_self {n : Nat} (hn : 0 < n) :
    sigmaSum n = ((List.range n).filter (isDivisor n)).sum + n := by
  unfold sigmaSum
  rw [List.range_succ, List.filter_append, sum_append_nat]
  have : (List.filter (isDivisor n) [n]) = [n] := by
    simp [List.filter, isDivisor, hn, Nat.mod_self]
  rw [this]
  simp

/-- For `n > 1` both `1` and `n` are divisors of `n`, hence `σ(n) ≥ n + 1`. -/
