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

theorem two_geom_sum (m : ℕ) : (∑ k ∈ range m, 2 ^ k) + 1 = 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ]; omega

/-- The crude bound `σ(k) ≤ k(k+1)/2`, coming from `divisors k ⊆ {0, …, k}`. -/
