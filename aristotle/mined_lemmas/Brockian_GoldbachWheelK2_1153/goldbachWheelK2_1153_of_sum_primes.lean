import Mathlib

open scoped BigOperators
open scoped Nat
open scoped Classical

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Brockian

/-- The new wheel modulus: the prime `1153`. -/
abbrev wheelModulus : ℕ := 1153


theorem goldbachWheelK2_1153_of_sum_primes {n a b : ℕ} (hab : n = a + b)
    (ha : a.Prime) (hb : b.Prime) (ha' : a ≠ 1153) (hb' : b ≠ 1153) :
    (a : ZMod wheelModulus) ∈ goldbachWheelSet wheelModulus (n : ZMod wheelModulus) := by
  have hp : Nat.Prime 1153 := by norm_num
  have key : ∀ c : ℕ, c.Prime → c ≠ 1153 → (c : ZMod 1153) ≠ 0 := by
    intro c hc hc'
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    exact hc' (((Nat.prime_dvd_prime_iff_eq hp hc).mp hdvd).symm)
  rw [mem_goldbachWheelSet]
  refine ⟨?_, ?_⟩
  · simpa [isUnit_iff_ne_zero] using key a ha ha'
  · have : ((n : ZMod wheelModulus) - (a : ZMod wheelModulus)) = (b : ZMod wheelModulus) := by
      subst hab; push_cast; ring
    rw [this]
    simpa [isUnit_iff_ne_zero] using key b hb hb'

end Brockian

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

