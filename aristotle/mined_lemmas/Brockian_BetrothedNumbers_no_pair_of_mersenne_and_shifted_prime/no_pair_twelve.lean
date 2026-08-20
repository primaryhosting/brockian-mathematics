/-
# No Pair Of Mersenne And Shifted Prime
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.no_pair_of_mersenne_and_shifted_prime
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# No Pair Of Mersenne And Shifted Prime
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.no_pair_of_mersenne_and_shifted_prime
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian.BetrothedNumbers

/-- `n` and `m` form a *betrothed* (quasi-amicable) pair: they are distinct positive integers
whose sums of divisors both equal `n + m + 1`. -/

theorem no_pair_twelve : ¬ ∃ m, IsBetrothedPair (2 ^ 2 * 3) m :=
  no_pair_of_mersenne_and_shifted_prime (k := 2) (p := 3) (by norm_num) (by norm_num)
    (by decide) (by norm_num) (by norm_num)

end Brockian.BetrothedNumbers

