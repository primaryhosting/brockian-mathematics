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

theorem brenierPot_convexOn [Nonempty ι] (hR : ∀ i, ‖g i‖ ≤ R) (hb : ∀ i, m ≤ b i) :
    ConvexOn ℝ Set.univ (brenierPot g b) := by
  refine ⟨convex_univ, ?_⟩
  rintro x - y - a c ha hc hac
  refine ciSup_le fun i => ?_
  have hx : inner ℝ (g i) x - (‖g i‖ ^ 2 / 2 + b i) ≤ brenierPot g b x :=
    le_ciSup (bddAbove_brenier_family hR hb x) i
  have hy : inner ℝ (g i) y - (‖g i‖ ^ 2 / 2 + b i) ≤ brenierPot g b y :=
    le_ciSup (bddAbove_brenier_family hR hb y) i
  have hlin : (inner ℝ (g i) (a • x + c • y) : ℝ)
      = a * inner ℝ (g i) x + c * inner ℝ (g i) y := by
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  have h1 : a * (inner ℝ (g i) x - (‖g i‖ ^ 2 / 2 + b i)) ≤ a * brenierPot g b x :=
    mul_le_mul_of_nonneg_left hx ha
  have h2 : c * (inner ℝ (g i) y - (‖g i‖ ^ 2 / 2 + b i)) ≤ c * brenierPot g b y :=
    mul_le_mul_of_nonneg_left hy hc
  have hkey : inner ℝ (g i) (a • x + c • y) - (‖g i‖ ^ 2 / 2 + b i)
      = a * (inner ℝ (g i) x - (‖g i‖ ^ 2 / 2 + b i))
        + c * (inner ℝ (g i) y - (‖g i‖ ^ 2 / 2 + b i)) := by
    rw [hlin]
    have : a * (‖g i‖ ^ 2 / 2 + b i) + c * (‖g i‖ ^ 2 / 2 + b i) = ‖g i‖ ^ 2 / 2 + b i := by
      rw [← add_mul, hac, one_mul]
    linarith
  rw [hkey]
  simp only [smul_eq_mul]
  linarith

