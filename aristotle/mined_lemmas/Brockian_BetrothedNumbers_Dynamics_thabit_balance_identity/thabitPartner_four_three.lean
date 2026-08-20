import Mathlib

/-!
# Thabit Balance Identity
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.Dynamics.thabit_balance_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open ArithmeticFunction

namespace Brockian.BetrothedNumbers.Dynamics

/-- The Thabit-style candidate `m = (2^k - 1)(p + 2)`. -/

lemma thabitPartner_four_three : thabitPartner 4 3 = 48 := by decide

/-- In the witness case `p + 3 = 6 < 32 = 2^(k+1)`, so `m = 75` is deficient. -/
example : sigma 1 (thabitM 4 3) < 2 * thabitM 4 3 := by
  rw [thabit_deficient_iff 4 3 sigmaCriterion_four_three]
  norm_num

end Brockian.BetrothedNumbers.Dynamics

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

