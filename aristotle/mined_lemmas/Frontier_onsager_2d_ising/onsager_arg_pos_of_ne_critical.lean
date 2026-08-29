import Mathlib

/-!
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real

namespace Frontier

/-! ## The finite-volume 2D Ising model on an `L × L` torus -/

/-- Shift a periodic (torus) index by one site. -/

theorem onsager_arg_pos_of_ne_critical (K θ φ : ℝ) (hK : 0 ≤ K) (hne : K ≠ criticalCoupling) :
    0 < Real.cosh (2 * K) ^ 2 - Real.sinh (2 * K) * (Real.cos θ + Real.cos φ) := by
  have hs : Real.sinh (2 * K) ≠ 1 := by
    rw [← sinh_two_criticalCoupling]
    intro h
    exact hne (by have := Real.sinh_injective h; linarith)
  have h0 : 0 < (Real.sinh (2 * K) - 1) ^ 2 := by
    have : Real.sinh (2 * K) - 1 ≠ 0 := sub_ne_zero.2 hs
    positivity
  exact lt_of_lt_of_le h0 (onsager_arg_lower_bound K θ φ hK)

/-- **Base case of Onsager's theorem**: at `K = 0` (infinite temperature) the exact
finite-volume free-energy density equals Onsager's expression for every `L ≥ 1`, and hence
the thermodynamic limit exists and agrees with Onsager's formula. -/
