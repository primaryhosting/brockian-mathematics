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

def LoeperMaxPrinciple (c : E → E → ℝ) (G : E → E → E) : Prop :=
  ∀ (x x₀ : E) (y : ℝ → E), IsCSegment G x₀ y → ∀ t ∈ Icc (0 : ℝ) 1,
    c x₀ (y t) - c x (y t) ≤
      max (c x₀ (y 0) - c x (y 0)) (c x₀ (y 1) - c x (y 1))

/-- The `x`-gradient of the quadratic cost is `x - y`. -/
