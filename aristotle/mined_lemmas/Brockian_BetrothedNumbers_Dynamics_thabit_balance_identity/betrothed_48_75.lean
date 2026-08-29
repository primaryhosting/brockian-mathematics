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

## Contents

For a Thabit-type candidate `m = (2 ^ k - 1) * (p + 2)` satisfying the delivered
sigma criterion `σ₁ m = (2 ^ (k + 1) - 1) * (p + 1)`, we prove the subtraction-free
balance identity

  `σ₁ m + 2 ^ (k + 1) = 2 * m + (p + 3)`

and deduce the deficient / perfect / abundant comparison `iff` theorems:
`m` is deficient (resp. perfect, abundant) exactly when `p + 3 < 2 ^ (k + 1)`
(resp. `=`, `>`).

The criterion is non-vacuous: `(k, p) = (4, 3)` gives `m = 75`, one half of the
betrothed (quasi-amicable) pair `(48, 75)`.
-/

set_option autoImplicit false

namespace Brockian.BetrothedNumbers.Dynamics

open ArithmeticFunction

/-- The Thabit-type candidate `m = (2 ^ k - 1) * (p + 2)`. -/

theorem betrothed_48_75 :
    sigma 1 48 = 48 + 75 + 1 ∧ sigma 1 75 = 48 + 75 + 1 := by
  constructor <;> decide

/-- Instance of the balance identity at the witness `(k, p) = (4, 3)`. -/
example : sigma 1 (thabitCandidate 4 3) + 2 ^ 5 = 2 * thabitCandidate 4 3 + (3 + 3) :=
  thabit_balance_identity 4 3 sigmaCriterion_four_three

/-- The witness `m = 75` is deficient, since `3 + 3 < 2 ^ 5`. -/
example : sigma 1 (thabitCandidate 4 3) < 2 * thabitCandidate 4 3 :=
  (thabit_deficient_iff 4 3 sigmaCriterion_four_three).2 (by norm_num)

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

