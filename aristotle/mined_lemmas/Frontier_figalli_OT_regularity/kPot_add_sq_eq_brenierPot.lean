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

theorem kPot_add_sq_eq_brenierPot [Nonempty ι] (hR : ∀ i, ‖g i‖ ≤ R) (hb : ∀ i, m ≤ b i)
    (x : EuclideanSpace ℝ (Fin n)) :
    kPot g b x + ‖x‖ ^ 2 / 2 = brenierPot g b x := by
  have hbdd : BddAbove (Set.range fun i => -sqCost x (g i) - b i) := by
    obtain ⟨C, hC⟩ := bddAbove_brenier_family hR hb x
    refine ⟨C - ‖x‖ ^ 2 / 2, ?_⟩
    rintro _ ⟨i, rfl⟩
    have hc : -sqCost x (g i) - b i + ‖x‖ ^ 2 / 2
        = inner ℝ (g i) x - (‖g i‖ ^ 2 / 2 + b i) := by
      have := norm_sub_pow_two_real x (g i)
      simp only [sqCost]
      rw [this, real_inner_comm]
      ring
    linarith [hC (Set.mem_range_self (f := fun i => inner ℝ (g i) x - (‖g i‖ ^ 2 / 2 + b i)) i)]
  rw [kPot, ciSup_add hbdd]
  refine congrArg _ (funext fun i => ?_)
  have := norm_sub_pow_two_real x (g i)
  simp only [sqCost]
  rw [this, real_inner_comm]
  ring

/-- The Brenier potential is a convex function (a supremum of affine functions). -/
