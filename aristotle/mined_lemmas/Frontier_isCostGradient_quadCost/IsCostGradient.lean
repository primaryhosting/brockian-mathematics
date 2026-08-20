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

def IsCostGradient (c : E → E → ℝ) (G : E → E → E) : Prop :=
  ∀ x y, HasGradientAt (fun x' => c x' y) (G x y) x

/-- A curve `y : ℝ → E` is a `c`-segment with base point `x₀` when the associated
momenta `∇ₓ c (x₀, y t)` depend affinely on `t`. -/
