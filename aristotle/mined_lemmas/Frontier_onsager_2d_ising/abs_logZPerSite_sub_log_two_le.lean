/-
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring; the required header is
-- reproduced verbatim as a module docstring immediately after the import below.)

import Mathlib

/-!
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
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

/-! ## The finite square-lattice Ising model on an `L × L` torus -/

/-- The cyclic shift `i ↦ i + 1` on `Fin L` (periodic boundary conditions). -/

lemma abs_logZPerSite_sub_log_two_le (L : ℕ) (hL : 0 < L) (K : ℝ) :
    |logZPerSite L K - Real.log 2| ≤ 2 * |K| := by
  obtain ⟨hlow, hhigh⟩ := isingZ_bounds L K
  have hN : (0 : ℝ) < (L : ℝ) ^ 2 := by positivity
  have hNe : ((L * L : ℕ) : ℝ) = (L : ℝ) ^ 2 := by push_cast; ring
  have hposZ := isingZ_pos L K
  have h2 : (0 : ℝ) < 2 ^ (L * L) := by positivity
  -- lower bound on log Z
  have hl : ((L : ℝ) ^ 2) * Real.log 2 - 2 * |K| * ((L : ℝ) ^ 2) ≤ Real.log (isingZ L K) := by
    have := Real.log_le_log (by positivity) hlow
    refine le_trans (le_of_eq ?_) this
    rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_pow, Real.log_exp, hNe]
    ring_nf
  have hh : Real.log (isingZ L K) ≤ ((L : ℝ) ^ 2) * Real.log 2 + 2 * |K| * ((L : ℝ) ^ 2) := by
    have := Real.log_le_log hposZ hhigh
    refine le_trans this (le_of_eq ?_)
    rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_pow, Real.log_exp, hNe]
  rw [abs_le]
  constructor
  · rw [logZPerSite, le_sub_iff_add_le, le_div_iff₀ hN]
    nlinarith [hl]
  · rw [logZPerSite, sub_le_iff_le_add, div_le_iff₀ hN]
    nlinarith [hh]

/-! ## An exactly solvable finite case -/

/-- On the `1 × 1` torus every bond is a self-bond, so the energy is `-2` for both
configurations. -/
