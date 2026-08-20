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

theorem brenierPot_lipschitz [Nonempty ι] (hR : ∀ i, ‖g i‖ ≤ R) (hb : ∀ i, m ≤ b i) :
    LipschitzWith R.toNNReal (brenierPot g b) := by
  have hR0 : 0 ≤ R := zero_le_R hR
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have h1 := brenierPot_le_add hR hb x y
  have h2 := brenierPot_le_add hR hb y x
  rw [norm_sub_rev] at h2
  have hd : dist (brenierPot g b x) (brenierPot g b y) ≤ R * ‖x - y‖ := by
    rw [Real.dist_eq, abs_sub_le_iff]
    constructor <;> linarith
  have : (R.toNNReal : ℝ) = R := Real.coe_toNNReal R hR0
  rw [this, dist_eq_norm]
  exact hd

/-- Rademacher: the Brenier potential is differentiable almost everywhere, so the optimal
transport map `T = ∇φ` is well defined a.e. -/
