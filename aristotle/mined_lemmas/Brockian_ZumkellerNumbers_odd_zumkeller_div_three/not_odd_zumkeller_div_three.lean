import Mathlib

namespace Brockian.ZumkellerNumbers

/-- `n` is *Zumkeller* if its divisors split into two sets of equal sum, expressed via
the half-sum characterization: some subset of the divisors sums to half of sigma(n). -/

theorem not_odd_zumkeller_div_three : ¬ (∀ n : ℕ, Odd n → Zumkeller n → 3 ∣ n) := by
  intro h
  exact not_three_dvd_5391411025 (h 5391411025 odd_5391411025 zumkeller_5391411025)

end Brockian.ZumkellerNumbers

