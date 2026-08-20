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

namespace Brockian.BetrothedNumbers.Dynamics

/-- The delivered **Thabit sigma criterion** for a Thabit-shaped candidate
`m = (2 ^ k - 1) * (p + 2)` with `1 ≤ k`:  the divisor sum of `m` is
`2 * m + (p + 3) - 2 ^ (k + 1)`.  The defining equation is stated over `ℤ`, so
that the truncated subtraction of `ℕ` plays no role. -/

theorem deficient_75 : Nat.Deficient 75 :=
  (thabit_balance_identity thabitSigmaCriterion_75).2.1.mpr (by norm_num)

end Brockian.BetrothedNumbers.Dynamics

