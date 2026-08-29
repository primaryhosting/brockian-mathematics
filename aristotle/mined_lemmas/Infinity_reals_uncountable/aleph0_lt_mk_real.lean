import Mathlib

/-!
# Reals Uncountable
Category: Frontier — Set Theory
Target: Infinity.reals_uncountable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` commands to precede every other command, including
-- module doc comments, so the header block above sits immediately after `import Mathlib`.

namespace Infinity

/-- `ℝ` is not a countable type. -/

theorem aleph0_lt_mk_real : Cardinal.aleph0 < Cardinal.mk ℝ := by
  rw [Cardinal.mk_real]
  exact Cardinal.aleph0_lt_continuum

end Infinity

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

