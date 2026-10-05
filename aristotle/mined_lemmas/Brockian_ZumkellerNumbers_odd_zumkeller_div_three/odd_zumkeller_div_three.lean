import Mathlib

namespace Brockian.ZumkellerNumbers

/-- `n` is *Zumkeller* if its divisors split into two sets of equal sum, expressed via
the half-sum characterization: some subset of the divisors sums to half of sigma(n). -/

theorem odd_zumkeller_div_three : ∀ n, Odd n → Zumkeller n → 3 ∣ n
-/

/-- **The conjecture "every odd Zumkeller number is divisible by 3" is false.**
The counterexample is `5391411025 = 5^2 * 7 * 11 * 13 * 17 * 19 * 23 * 29`. -/
