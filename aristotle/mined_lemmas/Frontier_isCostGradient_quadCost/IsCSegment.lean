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
open scoped ENNReal NNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

open MeasureTheory Set

/-! ### The Ma–Trudinger–Wang condition (Loeper's form) -/

section MTW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The quadratic transport cost `c(x,y) = ‖x - y‖²/2`. -/

def IsCSegment (G : E → E → E) (x₀ : E) (y : ℝ → E) : Prop :=
  ∀ t : ℝ, G x₀ (y t) = (1 - t) • G x₀ (y 0) + t • G x₀ (y 1)

/-- **Loeper's maximum principle** for a cost `c` with `x`-gradient field `G`: along any
`c`-segment based at `x₀`, the function `t ↦ c(x₀, y t) - c(x, y t)` attains its maximum
at the endpoints.  For smooth non-degenerate costs this is equivalent to the
Ma–Trudinger–Wang condition `MTW(0)` (non-negative cross-curvature in the weak sense),
which is the structural hypothesis under which optimal maps are regular. -/
