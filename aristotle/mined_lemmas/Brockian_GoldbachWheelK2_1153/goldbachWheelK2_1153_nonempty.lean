import Mathlib

open scoped BigOperators
open scoped Nat
open scoped Classical

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Brockian

/-- The new wheel modulus: the prime `1153`. -/
abbrev wheelModulus : ℕ := 1153


theorem goldbachWheelK2_1153_nonempty (n : ZMod wheelModulus) :
    (goldbachWheelSet wheelModulus n).Nonempty := by
  rw [← Finset.card_pos, GoldbachWheelK2_1153]
  split <;> norm_num

/-- The wheel really is a constraint satisfied by Goldbach representations: if an even number
`n` is a sum of two primes `a` and `b`, neither of which is the wheel modulus `1153`, then the
residue of `a` lies in the `K = 2` Goldbach wheel of `n` at `1153`. -/
