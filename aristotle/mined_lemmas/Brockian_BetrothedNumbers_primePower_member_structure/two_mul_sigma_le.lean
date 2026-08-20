import Mathlib

/-!
# Prime Power Member Structure
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.primePower_member_structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Nat
open scoped Classical

set_option maxHeartbeats 1000000

namespace Brockian.BetrothedNumbers

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

/-- `IsBetrothedPair m n` : `m` and `n` form a betrothed (quasi-amicable) pair, i.e. the sum of
the nontrivial divisors (all divisors except `1` and the number itself) of each equals the other.
Equivalently `σ m = σ n = m + n + 1`.

The classical definition additionally requires `m ≠ n`; that hypothesis is not needed for any of
the results below, so it is omitted here (making the statements slightly stronger). -/

lemma two_mul_sigma_le {q : ℕ} : 2 * σ 1 q ≤ q * (q + 1) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  have hsub : q.divisors ⊆ Finset.range (q + 1) := by
    intro d hd
    exact Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.divisor_le hd))
  have h1 : σ 1 q ≤ ∑ i ∈ Finset.range (q + 1), i := by
    rw [sigma_one_apply]
    exact Finset.sum_le_sum_of_subset hsub
  have h2 : (∑ i ∈ Finset.range (q + 1), i) * 2 = (q + 1) * q :=
    Finset.sum_range_id_mul_two (q + 1)
  calc 2 * σ 1 q ≤ (∑ i ∈ Finset.range (q + 1), i) * 2 := by omega
    _ = (q + 1) * q := h2
    _ = q * (q + 1) := Nat.mul_comm _ _

