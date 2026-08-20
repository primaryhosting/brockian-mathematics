/-
Enumeration data for `Brockian.GoldbachWheelK2_1327`.

For every `n` with `2 ≤ n ≤ 1327` we exhibit an explicit pair of primes summing
to the even number `2 * n`, i.e. Goldbach's conjecture is verified for all even
numbers up to twice the wheel modulus `1327`.
-/
import Mathlib

set_option maxRecDepth 10000

namespace Brockian

/-- `GoldbachRep n` states that `n` is a sum of two primes. -/

def WheelK2 : Finset ℕ := {1, 5}

/-- Every prime larger than `3` lies in the `K = 2` wheel `{1, 5}` modulo `6`. -/
