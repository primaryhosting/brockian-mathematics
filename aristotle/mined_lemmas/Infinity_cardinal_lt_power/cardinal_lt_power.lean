/-
Lean requires `import` lines to precede any module docstring, so the required
header is reproduced verbatim inside this comment (and again as the module
docstring below, after the import).

/-!
# Cardinal Lt Power
Category: Frontier — Set Theory
Target: Infinity.cardinal_lt_power
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/
import Mathlib

/-!
# Cardinal Lt Power
Category: Frontier — Set Theory
Target: Infinity.cardinal_lt_power
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Infinity

/-- Cantor's theorem in cardinal form: `c < 2 ^ c` for every cardinal `c`.
This is `Cardinal.cantor` in Mathlib. -/

theorem cardinal_lt_power (c : Cardinal) : c < 2 ^ c :=
  Cardinal.cantor c

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

