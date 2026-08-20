/-
# Ramsey 3 3
Category: Pure Mathematics
Target: Math.ramsey_3_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ramsey 3 3
Category: Pure Mathematics
Target: Math.ramsey_3_3
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

set_option grind.warning false

namespace Math

/-- Pigeonhole: among five booleans, three are equal. -/

theorem pentagon_no_mono_triangle :
    ∀ a b c : Fin 5, a < b → b < c →
      ¬(pentagon a b = pentagon a c ∧ pentagon a c = pentagon b c) := by
  decide +kernel

/-- **R(3,3) = 6**: every 2-coloring of the edges of `K₆` (edges being the pairs `a < b`,
coloured by `f a b : Bool`) contains a monochromatic triangle, while there is a 2-coloring
of the edges of `K₅` with no monochromatic triangle. -/
