/-
Primality certificates for the primes occurring in the level-2 Goldbach wheel
witness table for the modulus `947`.

These are auxiliary facts used by `Brockian.GoldbachWheelK2_947`.
-/
import Mathlib.Tactic.NormNum.Prime

namespace Brockian.Wheel


theorem GoldbachWheelK2_5 : GoldbachWheelK2 5 := by
  refine goldbachWheelK2_of_bounded_goldbach (by norm_num) (by norm_num) ?_
  intro n hn h4 h10
  interval_cases n
  · exact ⟨2, 2, Nat.prime_two, Nat.prime_two, by norm_num⟩
  · exact absurd hn (by decide)
  · exact ⟨3, 3, Nat.prime_three, Nat.prime_three, by norm_num⟩
  · exact absurd hn (by decide)
  · exact ⟨3, 5, Nat.prime_three, by norm_num, by norm_num⟩
  · exact absurd hn (by decide)
  · exact ⟨5, 5, by norm_num, by norm_num, by norm_num⟩

end Brockian

/-
# The wheel modulus 947

Verification that `947` belongs to the `Brockian.GoldbachWheelK2` family of
level-2 Goldbach wheel moduli.
-/
import RequestProject.GoldbachWheelBasic
import RequestProject.GoldbachWheelPrimes
import Mathlib.Tactic.IntervalCases

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Brockian

/-- The modulus `947` is a level-2 Goldbach wheel modulus: every residue class
mod `947` is of the form `p + q` with `p`, `q` prime and `p + q ≤ 1894`. -/
