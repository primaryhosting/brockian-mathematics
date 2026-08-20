/-
# Prime Power Member Structure
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.primePower_member_structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Prime Power Member Structure
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.primePower_member_structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace Brockian.BetrothedNumbers

/-- `m` and `n` form a *betrothed* (quasi-amicable) pair: both are positive, distinct, and the
sum of the divisors of each equals `m + n + 1` (equivalently, the sum of the *proper* divisors of
each one is the other one plus one). -/

lemma isBetrothedPair_48_75 : IsBetrothedPair 48 75 :=
  ⟨by norm_num, by norm_num, by norm_num, by decide, by decide⟩

/-- Both members of a betrothed pair cannot be prime powers. -/
