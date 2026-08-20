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

theorem affine_le_max {a b t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    (1 - t) * a + t * b ≤ max a b := by
  nlinarith [le_max_left a b, le_max_right a b]

omit [CompleteSpace E] in
/-- The quadratic cost satisfies the Ma–Trudinger–Wang condition, in Loeper's form. -/
