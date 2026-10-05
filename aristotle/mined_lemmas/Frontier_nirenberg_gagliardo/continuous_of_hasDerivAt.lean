import Mathlib

/-!
# Nirenberg Gagliardo
Category: Frontier Abel
Target: Frontier.nirenberg_gagliardo
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

open MeasureTheory

namespace Frontier

/-- Auxiliary: a differentiable function is continuous. -/

private lemma continuous_of_hasDerivAt {u u' : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u' x) x) :
    Continuous u :=
  continuous_iff_continuousAt.2 fun x => (hu x).continuousAt

/-- Auxiliary: from a point outside a large ball the function vanishes; we pick a base point
to the left of any given `x`. -/
