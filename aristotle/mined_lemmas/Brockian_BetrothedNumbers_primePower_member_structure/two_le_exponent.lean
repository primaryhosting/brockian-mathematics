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

lemma two_le_exponent {p a n : ℕ} (hp : p.Prime) (h : IsBetrothedPair (p ^ a) n) : 2 ≤ a := by
  have hpe := partner_eq hp h
  rcases a with _ | _ | a
  · simp at hpe
  · simp at hpe
    have := h.2.1
    omega
  · omega

/-- No power of two is a member of a betrothed pair. -/
