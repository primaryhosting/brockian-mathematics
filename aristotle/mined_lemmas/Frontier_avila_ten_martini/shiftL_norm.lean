/-
# Avila Ten Martini
Category: Frontier — Fields Medal Work
Target: Frontier.avila_ten_martini
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

noncomputable section

/-! ## The Hilbert space `ℓ²(ℤ)` -/

/-- The complex Hilbert space `ℓ²(ℤ)`, on which the almost Mathieu operator acts. -/
abbrev Hl2 := lp (fun _ : ℤ => ℂ) 2

/-- Auxiliary: the real exponent attached to `p = 2`. -/

theorem shiftL_norm (k : ℤ) (u : Hl2) : ‖shiftL k u‖ ≤ ‖u‖ := by
  apply lp.norm_le_of_tsum_le (by norm_num) (norm_nonneg u)
  have h1 : ∑' i : ℤ, ‖(shiftL k u : ℤ → ℂ) i‖ ^ ((2 : ℝ≥0∞)).toReal
      = ∑' i : ℤ, ‖(u : ℤ → ℂ) i‖ ^ ((2 : ℝ≥0∞)).toReal :=
    (Equiv.addRight k).tsum_eq (fun i => ‖(u : ℤ → ℂ) i‖ ^ ((2 : ℝ≥0∞)).toReal)
  rw [h1, lp.norm_rpow_eq_tsum (by norm_num)]

/-- The shift `(S_k u)(n) = u(n + k)` as a bounded operator on `ℓ²(ℤ)`. -/
