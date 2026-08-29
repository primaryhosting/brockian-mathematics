import Mathlib

/-!
# Prime Power Member Structure
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.primePower_member_structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open ArithmeticFunction Finset

namespace Brockian
namespace BetrothedNumbers

/-- `IsBetrothedPair m n` says that `(m, n)` is a betrothed (quasi-amicable) pair: two distinct
positive integers, each of whose sum of divisors equals `m + n + 1`. -/

theorem two_mul_sigma_one_le (k : ℕ) : 2 * sigma 1 k ≤ k * (k + 1) := by
  have h1 : sigma 1 k = ∑ d ∈ k.divisors, d := sigma_one_apply k
  have h2 : k.divisors ⊆ range (k + 1) := fun d hd =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.divisor_le hd))
  have h3 : ∑ d ∈ k.divisors, d ≤ ∑ d ∈ range (k + 1), d :=
    Finset.sum_le_sum_of_subset h2
  have h4 : (∑ i ∈ range (k + 1), i) * 2 = (k + 1) * k := by
    simpa using Finset.sum_range_id_mul_two (k + 1)
  have h5 : k * (k + 1) = (k + 1) * k := Nat.mul_comm _ _
  omega

