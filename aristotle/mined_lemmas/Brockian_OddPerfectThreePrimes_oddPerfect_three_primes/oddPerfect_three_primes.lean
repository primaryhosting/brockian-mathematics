import Mathlib
namespace Brockian.OddPerfectThreePrimes

open Finset

/-- For a prime `p`, `(p-1) * σ₁(p^a) = p^(a+1) - 1 < p * p^a`. -/

theorem oddPerfect_three_primes {n : ℕ} (ho : Odd n) (hp : Nat.Perfect n) :
    3 ≤ n.primeFactors.card := by
  by_contra hcard
  rw [not_le] at hcard
  have hn0 : 0 < n := hp.2
  have hsum : ∑ i ∈ n.divisors, i = 2 * n :=
    (Nat.perfect_iff_sum_divisors_eq_two_mul hn0).mp hp
  have hn1 : 1 < n := by
    rcases Nat.lt_or_ge n 2 with h | h
    · have hn : n = 1 := by omega
      subst hn
      rw [Nat.divisors_one] at hsum
      simp at hsum
    · exact h
  have hne : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr hn1
  have key := sigma_prod_bound hn0.ne' hne
  rw [hsum] at key
  have h3 : ∀ p ∈ n.primeFactors, 3 ≤ p := by
    intro p hpm
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpm
    have hdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hpm
    have hodd : Odd p := by
      rcases hdvd with ⟨c, rfl⟩
      exact (Nat.odd_mul.mp ho).1
    have hp2 : p ≠ 2 := by
      rintro rfl
      simp [Nat.odd_iff] at hodd
    have := hpp.two_le
    omega
  have hle := prod_le_two_mul_prod_pred (by omega : n.primeFactors.card ≤ 2) h3
  nlinarith [key, hle, hn0]

end Brockian.OddPerfectThreePrimes

