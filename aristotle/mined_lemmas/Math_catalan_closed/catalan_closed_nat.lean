/-
# Catalan Closed
Category: Pure Mathematics
Target: Math.catalan_closed
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` before any module docstring `/-! ... -/`, so the
-- header above is repeated below in module-docstring form.)
import Mathlib

/-!
# Catalan Closed
Category: Pure Mathematics
Target: Math.catalan_closed
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- Key Mathlib identity (`succ_mul_catalan_eq_centralBinom`), restated with
`Nat.choose (2 * n) n` in place of `Nat.centralBinom n`:
`(n + 1) * catalan n = C(2n, n)`. -/

theorem catalan_closed_nat (n : ℕ) :
    catalan n = Nat.choose (2 * n) n / (n + 1) := by
  rw [catalan_eq_centralBinom_div]
  rfl

end Math

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

