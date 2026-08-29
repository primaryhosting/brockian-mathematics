import Mathlib

namespace Brockian.ZumkellerNumbers

/-- `n` is *Zumkeller* if its divisors split into two sets of equal sum, expressed via
the half-sum characterization: some subset of the divisors sums to half of sigma(n). -/

theorem not_zumkeller_of_deficient (n : ℕ) (hn : 0 < n)
    (h : ∑ d ∈ n.divisors, d < 2 * n) : ¬ Zumkeller n := by
  rintro ⟨S, hS, hsum⟩
  have hnd : n ∈ n.divisors := Nat.mem_divisors_self n hn.ne'
  by_cases hmem : n ∈ S
  · have : n ≤ ∑ d ∈ S, d :=
      Finset.single_le_sum (f := fun d => d) (fun i _ => Nat.zero_le i) hmem
    omega
  · have h1 : ∑ d ∈ insert n S, d ≤ ∑ d ∈ n.divisors, d :=
      Finset.sum_le_sum_of_subset (Finset.insert_subset hnd hS)
    rw [Finset.sum_insert hmem] at h1
    omega

end Brockian.ZumkellerNumbers

