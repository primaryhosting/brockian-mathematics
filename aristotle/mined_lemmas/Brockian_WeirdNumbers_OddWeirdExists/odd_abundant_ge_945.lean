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
# Odd Weird Exists
Category: Brockian Conjecture
Target: Brockian.WeirdNumbers.OddWeirdExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Weird Exists
Category: Brockian Conjecture
Target: Brockian.WeirdNumbers.OddWeirdExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 4000000
set_option maxHeartbeats 4000000

namespace Brockian
namespace WeirdNumbers

/-- `n` is *semiperfect* (pseudoperfect) if `n` is positive and some set of proper divisors
of `n` sums to `n`. -/

theorem odd_abundant_ge_945 {n : ℕ} (hodd : Odd n) (habund : n.Abundant) : 945 ≤ n := by
  have key : ∀ m < 945, Odd m → ¬ m.Abundant := by decide
  by_contra h
  push_neg at h
  exact key n h hodd habund

/-- Every odd weird number is at least `947`. -/
