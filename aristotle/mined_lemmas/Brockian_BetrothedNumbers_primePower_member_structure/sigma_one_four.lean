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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian.BetrothedNumbers

open ArithmeticFunction
open scoped ArithmeticFunction
/-- `m` and `n` form a *betrothed* (quasi-amicable) pair: both are positive and distinct, and
the sum of the divisors of each, other than the number itself and `1`, is the other member;
equivalently `sigma m = sigma n = m + n + 1`. -/

theorem sigma_one_four : ArithmeticFunction.sigma 1 4 = 7 := by
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, sigma_one_prime_pow Nat.prime_two]
  decide

/-- **Hagis–Lord, Proposition 4.**  If a prime power `p ^ a` is a member of a betrothed
(quasi-amicable) pair, then `p` is odd, the exponent `a` is odd and greater than `3`, and the
partner `n` is even. -/
