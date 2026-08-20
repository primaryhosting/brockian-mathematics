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

def GoldbachRep (n : ℕ) : Prop := ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n

/-- Every even number `2 * n` with `2 ≤ n ≤ 1327` is a sum of two primes,
verified by explicit witnesses. -/
