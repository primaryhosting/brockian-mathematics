/-!
# Value At Zero
Category: Riemann Program
Target: Riemann.Zeta.value_at_zero
Statement: riemannZeta 0 = -1 / 2. (Use Mathlib's riemannZeta_zero.)
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-!
# Value At Zero
Category: Riemann Program
Target: Riemann.Zeta.value_at_zero
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Riemann.Zeta

/-- The Riemann zeta function at `0` equals `-1/2`.

This follows immediately from Mathlib's `riemannZeta_zero : riemannZeta 0 = -1 / 2`. -/
theorem value_at_zero : riemannZeta 0 = -1 / 2 := riemannZeta_zero

end Riemann.Zeta

