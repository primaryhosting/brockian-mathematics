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

/-- Partial derivative `∂L/∂q` of a Lagrangian `L q v t` with respect to the position `q`. -/

theorem dLdq_eq_zero_of_translationInvariant {L : ℝ → ℝ → ℝ → ℝ}
    (h : TranslationInvariant L) (q v t : ℝ) : dLdq L q v t = 0 := by
  have hconst : (fun x : ℝ => L x v t) = fun _ : ℝ => L 0 v t := by
    funext x
    simpa using h x 0 v t
  simp [dLdq, hconst]

/-- **Noether's theorem for spatial translations (1D).**

If a Lagrangian `L q v t` is invariant under translations of the position coordinate, then
along any path `q` satisfying the Euler–Lagrange equation
`d/dt (∂L/∂v (q t, q̇ t, t)) = ∂L/∂q (q t, q̇ t, t)`,
the canonical momentum `p t = ∂L/∂v (q t, q̇ t, t)` is conserved. -/
