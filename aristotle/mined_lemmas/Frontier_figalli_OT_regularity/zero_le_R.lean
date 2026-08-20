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

set_option grind.warning false

namespace Frontier

/-! ## Partial derivatives of a cost function in coordinates -/

section MTW

variable {n : ℕ}

/-- Partial derivative of a cost `c x y` in the `i`-th coordinate of the source variable `x`. -/

lemma zero_le_R [Nonempty ι] (hR : ∀ i, ‖g i‖ ≤ R) : 0 ≤ R :=
  le_trans (norm_nonneg (g (Classical.arbitrary ι))) (hR _)

/-- The Kantorovich potential for the quadratic cost differs from the convex Brenier
potential exactly by `|x|²/2`; in particular the Brenier potential is convex. -/
