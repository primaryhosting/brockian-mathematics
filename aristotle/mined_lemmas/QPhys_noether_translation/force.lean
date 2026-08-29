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

noncomputable def force (L : ℝ → ℝ → ℝ → ℝ) (q : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv (fun x => L t x (deriv q t)) (q t)

/-- If the Lagrangian is invariant under spatial translations, the generalized force
vanishes identically. -/
