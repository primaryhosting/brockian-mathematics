/-
# Figalli OT Regularity
Category: Frontier — Fields Medal Work
Target: Frontier.figalli_OT_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Figalli OT Regularity
Category: Frontier — Fields Medal Work
Target: Frontier.figalli_OT_regularity
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

namespace Frontier

/-! ## The cost function and the Ma–Trudinger–Wang condition -/

/-- The quadratic (Brenier) transport cost `c(x,y) = ‖x - y‖² / 2` on a real inner product
space. -/

noncomputable def quadCost {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E) : ℝ := ‖x - y‖ ^ 2 / 2

/-- **Loeper's maximum principle**, the geometric reformulation of the
Ma–Trudinger–Wang condition (A3w) used in the regularity theory of optimal transport.
For a cost `c` whose `c`-segments are straight segments it reads: for all `x, z` and all
`y₀, y₁`, the function `t ↦ c x yₜ - c z yₜ` along the segment `yₜ = (1-t) y₀ + t y₁`
is bounded by its values at the endpoints. -/
