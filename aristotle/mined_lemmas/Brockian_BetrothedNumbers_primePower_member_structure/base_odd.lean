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

lemma base_odd {p a n : ℕ} (hp : p.Prime) (h : IsBetrothedPair (p ^ a) n) : Odd p := by
  rcases hp.eq_two_or_odd' with rfl | hodd
  · exact absurd h not_two_pow
  · exact hodd

/-- The exponent of a prime-power member of a betrothed pair is odd. -/
