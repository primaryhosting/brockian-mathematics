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

lemma geomSum_mod_two {p : ℕ} (hp : Odd p) (a : ℕ) :
    (∑ i ∈ Finset.range a, p ^ i) % 2 = a % 2 := by
  induction a with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have : p ^ k % 2 = 1 := Nat.odd_iff.mp hp.pow
    omega

/-- Partner formula: if `p ^ a` belongs to a betrothed pair with partner `n`, then
`n + 1 = 1 + p + ⋯ + p ^ (a - 1)`. -/
