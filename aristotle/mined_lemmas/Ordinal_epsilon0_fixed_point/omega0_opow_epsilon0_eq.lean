import Mathlib

/-!
# Epsilon 0 Fixed Point
Category: Frontier Wave 2 (deeper machinery)
Target: Ordinal.epsilon0_fixed_point
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` lines to precede every other piece of content in a file
-- (including doc comments), so the header block above sits immediately after the single
-- `import Mathlib` line rather than on line 1.

namespace Ordinal

/-- `ε₀` is a fixed point of ordinal `ω`-exponentiation, and it is the least such ordinal:
`IsLeast {o | ω ^ o = o} ε₀`. -/

theorem omega0_opow_epsilon0_eq : ω ^ (ε₀ : Ordinal) = ε₀ :=
  epsilon0_fixed_point.1

end Ordinal

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

