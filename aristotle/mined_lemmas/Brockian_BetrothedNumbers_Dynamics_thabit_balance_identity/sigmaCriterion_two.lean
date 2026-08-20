/-
# Thabit Balance Identity
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.Dynamics.thabit_balance_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Thabit Balance Identity
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.Dynamics.thabit_balance_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Nat
open scoped ArithmeticFunction.sigma

set_option maxHeartbeats 1000000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian.BetrothedNumbers.Dynamics

/--
The *delivered sigma criterion* for a Thabit-type parameter pair `(k, p)` and a candidate
number `m`:

* `m` is the Thabit-type value `(2 ^ k - 1) * (p + 2)`, and
* the divisor sum of `m` satisfies the subtraction-free relation
  `σ m + (p + 1) = 2 ^ (k + 1) * (p + 1)`
  (i.e. `σ m = (2 ^ (k + 1) - 1) * (p + 1)`, stated without natural subtraction).
-/

theorem sigmaCriterion_two : SigmaCriterion 1 0 2 := by
  constructor
  · norm_num
  · decide

end Brockian.BetrothedNumbers.Dynamics

-- Axiom audit
#print axioms Brockian.BetrothedNumbers.Dynamics.thabit_balance_identity
#print axioms Brockian.BetrothedNumbers.Dynamics.thabit_deficient_iff
#print axioms Brockian.BetrothedNumbers.Dynamics.thabit_perfect_iff
#print axioms Brockian.BetrothedNumbers.Dynamics.thabit_abundant_iff
#print axioms Brockian.BetrothedNumbers.Dynamics.thabit_sigma_eq
#print axioms Brockian.BetrothedNumbers.Dynamics.thabit_balance_identity_int
#print axioms Brockian.BetrothedNumbers.Dynamics.sigmaCriterion_two

import Mathlib

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

