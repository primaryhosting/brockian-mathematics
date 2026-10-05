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

theorem odd_weird_ge_947 {n : ℕ} (hodd : Odd n) (hw : Weird n) : 947 ≤ n := by
  have h945 := odd_abundant_ge_945 hodd hw.1
  have hpar : n % 2 = 1 := Nat.odd_iff.1 hodd
  have hne : n ≠ 945 := by
    rintro rfl
    exact hw.not_dvd_945 dvd_rfl
  omega

/-! ## Conditional reduction for the Brockian statement -/

/-- **Reduction.**  If an odd weird number exists at all, then there is one that is at least
`947`, is not divisible by `945`, and none of whose divisors is semiperfect. -/
