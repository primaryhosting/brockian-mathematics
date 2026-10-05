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

theorem oddWeirdExists_iff :
    OddWeirdExists ↔
      ∃ n : ℕ, Odd n ∧ Weird n ∧ 947 ≤ n ∧ ¬ (945 ∣ n) ∧ ∀ d, d ∣ n → ¬ Semiperfect d := by
  constructor
  · rintro ⟨n, hodd, hw⟩
    exact ⟨n, hodd, hw, odd_weird_ge_947 hodd hw, hw.not_dvd_945,
      fun d hd => hw.no_semiperfect_divisor hd⟩
  · rintro ⟨n, hodd, hw, -⟩
    exact ⟨n, hodd, hw⟩

end WeirdNumbers
end Brockian

