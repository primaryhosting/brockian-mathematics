import Mathlib

namespace Brockian.ZumkellerNumbers

/-- `n` is *Zumkeller* if its divisors split into two sets of equal sum, expressed via
the half-sum characterization: some subset of the divisors sums to half of sigma(n). -/

lemma sum_divisors_mod_two {n : ℕ} (hodd : Odd n) :
    (∑ d ∈ n.divisors, d) % 2 = n.divisors.card % 2 := by
  rw [Finset.sum_nat_mod]
  rw [Finset.sum_congr rfl
    (fun d hd => Nat.odd_iff.mp (odd_of_dvd_odd hodd (Nat.dvd_of_mem_divisors hd)))]
  simp

/-- A nonzero square has an odd number of divisors. -/
