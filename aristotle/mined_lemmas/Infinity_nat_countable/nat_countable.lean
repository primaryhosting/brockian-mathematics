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

import Mathlib
-- (Lean requires `import` to be the first command; the requested header follows.)

/-!
# Nat Countable
Category: Frontier — Set Theory
Target: Infinity.nat_countable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Infinity

/-- `ℕ` is countably infinite: it is a `Countable` type and an `Infinite` type. -/

theorem nat_countable : Countable ℕ ∧ Infinite ℕ :=
  ⟨inferInstance, inferInstance⟩

end Infinity

