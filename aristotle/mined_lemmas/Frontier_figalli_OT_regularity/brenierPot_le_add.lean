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

lemma brenierPot_le_add [Nonempty ι] (hR : ∀ i, ‖g i‖ ≤ R) (hb : ∀ i, m ≤ b i)
    (x y : EuclideanSpace ℝ (Fin n)) :
    brenierPot g b x ≤ brenierPot g b y + R * ‖x - y‖ := by
  refine ciSup_le fun i => ?_
  have hy : inner ℝ (g i) y - (‖g i‖ ^ 2 / 2 + b i) ≤ brenierPot g b y :=
    le_ciSup (bddAbove_brenier_family hR hb y) i
  have hsplit : (inner ℝ (g i) x : ℝ) = inner ℝ (g i) y + inner ℝ (g i) (x - y) := by
    rw [inner_sub_right]; ring
  have hle : (inner ℝ (g i) (x - y) : ℝ) ≤ R * ‖x - y‖ :=
    le_trans (real_inner_le_norm _ _) (mul_le_mul_of_nonneg_right (hR i) (norm_nonneg _))
  rw [hsplit]
  linarith

/-- The Brenier potential is globally `R`-Lipschitz when the targets have norm at most `R`. -/
