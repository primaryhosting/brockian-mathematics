import Mathlib
/-!
# Prime Power Member Structure
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.primePower_member_structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 1000000

namespace Brockian
namespace BetrothedNumbers

open Finset ArithmeticFunction

/-- A pair of *betrothed* (quasi-amicable) numbers: two distinct positive integers each of
whose divisor sums equals the sum of the two numbers plus one. -/

lemma sigma_one_ge_of_three_dvd {q : ℕ} (h3 : 3 ∣ q) (h9 : 9 < q) :
    q + q / 3 + 4 ≤ ArithmeticFunction.sigma 1 q := by
  obtain ⟨r, rfl⟩ := h3
  have hr : 3 < r := by omega
  have hdiv : 3 * r / 3 = r := by omega
  have hsub : ({1, 3, r, 3 * r} : Finset ℕ) ⊆ (3 * r).divisors := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rw [Nat.mem_divisors]
    refine ⟨?_, by omega⟩
    rcases hd with rfl | rfl | rfl | rfl
    · exact one_dvd _
    · exact ⟨r, rfl⟩
    · exact ⟨3, by ring⟩
    · exact dvd_rfl
  have hsum : ∑ d ∈ ({1, 3, r, 3 * r} : Finset ℕ), d = 1 + 3 + r + 3 * r := by
    rw [Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp; omega),
      Finset.sum_insert (by simp; omega), Finset.sum_singleton]
    ring
  have h2 : 1 + 3 + r + 3 * r ≤ ∑ d ∈ (3 * r).divisors, d := by
    simpa [hsum] using Finset.sum_le_sum_of_subset (f := fun d => d) hsub
  rw [ArithmeticFunction.sigma_one_apply, hdiv]
  omega

/-- The divisor sum of a prime. -/
