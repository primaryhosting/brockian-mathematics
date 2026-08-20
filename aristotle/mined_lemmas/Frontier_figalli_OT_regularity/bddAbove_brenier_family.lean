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

lemma bddAbove_brenier_family [Nonempty ι] (hR : ∀ i, ‖g i‖ ≤ R) (hb : ∀ i, m ≤ b i)
    (x : EuclideanSpace ℝ (Fin n)) :
    BddAbove (Set.range fun i => inner ℝ (g i) x - (‖g i‖ ^ 2 / 2 + b i)) := by
  refine ⟨R * ‖x‖ - m, ?_⟩
  rintro _ ⟨i, rfl⟩
  have h1 : (inner ℝ (g i) x : ℝ) ≤ ‖g i‖ * ‖x‖ := real_inner_le_norm _ _
  have h2 : ‖g i‖ * ‖x‖ ≤ R * ‖x‖ :=
    mul_le_mul_of_nonneg_right (hR i) (norm_nonneg x)
  have h3 : (0 : ℝ) ≤ ‖g i‖ ^ 2 / 2 := by positivity
  have h4 : m ≤ b i := hb i
  linarith

