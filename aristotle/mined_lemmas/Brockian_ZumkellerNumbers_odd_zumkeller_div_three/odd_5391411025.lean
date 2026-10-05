import Mathlib

namespace Brockian.ZumkellerNumbers

/-- `n` is *Zumkeller* if its divisors split into two sets of equal sum, expressed via
the half-sum characterization: some subset of the divisors sums to half of sigma(n). -/

theorem odd_5391411025 : Odd (5391411025 : ℕ) := by
  rw [Nat.odd_iff]

/-- `5391411025` is not divisible by `3`. -/
