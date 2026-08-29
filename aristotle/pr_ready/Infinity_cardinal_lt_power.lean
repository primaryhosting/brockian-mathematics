/-!
# Cardinal Lt Power
Category: Frontier — Set Theory
Target: Infinity.cardinal_lt_power
Statement: Cantor's cardinal inequality: for every cardinal c, c < 2 ^ c. (Use Mathlib's Cardinal.cantor.)
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

namespace Infinity

/-- Cantor's theorem for cardinals: every cardinal `c` satisfies `c < 2 ^ c`. -/
theorem cardinal_lt_power (c : Cardinal) : c < 2 ^ c :=
  Cardinal.cantor c

end Infinity

