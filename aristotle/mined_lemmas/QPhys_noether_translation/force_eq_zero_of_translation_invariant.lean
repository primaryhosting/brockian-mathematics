/-
# Noether Translation
Category: Quantum Physics
Target: QPhys.noether_translation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Noether Translation
Category: Quantum Physics
Target: QPhys.noether_translation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

/-- The canonical momentum of a one–dimensional Lagrangian system.

`L t x v` is the Lagrangian evaluated at time `t`, position `x` and velocity `v`,
and `q` is a path.  The canonical momentum along the path is
`p (t) = (∂L/∂v) (t, q t, q̇ t)`. -/

theorem force_eq_zero_of_translation_invariant
    (L : ℝ → ℝ → ℝ → ℝ) (q : ℝ → ℝ)
    (hinv : ∀ s t x v, L t (x + s) v = L t x v) (t : ℝ) :
    force L q t = 0 := by
  have hconst : (fun x => L t x (deriv q t)) = fun _ => L t 0 (deriv q t) := by
    funext x
    have := hinv x t 0 (deriv q t)
    simpa using this
  simp [force, hconst]

/-- **Noether's theorem for spatial translations (1D).**

If the Lagrangian `L` is invariant under translations of the position variable
(`hinv`), and the path `q` satisfies the Euler–Lagrange equation
`d/dt (∂L/∂v) = ∂L/∂x` (`hEL`), then the canonical momentum
`p t = (∂L/∂v) (t, q t, q̇ t)` is conserved. -/
