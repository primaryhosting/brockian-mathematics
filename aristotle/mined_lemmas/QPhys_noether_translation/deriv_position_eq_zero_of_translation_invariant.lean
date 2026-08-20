/-
# Noether Translation
Category: Quantum Physics
Target: QPhys.noether_translation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QPhys

/-- **Key lemma.** If a Lagrangian `L : ℝ → ℝ → ℝ` (position, velocity) is invariant under
translations of the position variable, then its partial derivative with respect to position
vanishes identically. -/

theorem deriv_position_eq_zero_of_translation_invariant
    (L : ℝ → ℝ → ℝ) (hinv : ∀ a x u, L (x + a) u = L x u) (x u : ℝ) :
    deriv (fun y => L y u) x = 0 := by
  have hconst : (fun y => L y u) = fun _ => L 0 u := by
    funext y
    simpa using hinv y 0 u
  rw [hconst]
  simp

/-- **Noether's theorem for translations (1D).**

Let `L : ℝ → ℝ → ℝ` be a Lagrangian, written `L q v` in terms of position and velocity, and let
`q, v : ℝ → ℝ` be a trajectory and its velocity.  The canonical momentum along the trajectory is
`p t = ∂L/∂v (q t, v t)`.

Assuming
* translation invariance: `L (x + a) u = L x u` for all `a, x, u`, and
* the Euler–Lagrange equation: `d/dt (∂L/∂v (q t, v t)) = ∂L/∂q (q t, v t)`,

the momentum is conserved: it takes the same value at all times. -/
