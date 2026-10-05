import Mathlib

namespace Brockian.ZumkellerNumbers

/-- `n` is *Zumkeller* if its divisors split into two sets of equal sum, expressed via
the half-sum characterization: some subset of the divisors sums to half of sigma(n). -/

lemma odd_of_dvd_odd {n d : ℕ} (hodd : Odd n) (hd : d ∣ n) : Odd d := by
  obtain ⟨c, rfl⟩ := hd
  exact (Nat.odd_mul.mp hodd).1

/-- For odd `n`, the sum of divisors has the same parity as the number of divisors. -/
