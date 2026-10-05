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

noncomputable def momentum (L : ℝ → ℝ → ℝ → ℝ) (q : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv (fun v => L t (q t) v) (deriv q t)

/-- The generalized force of a one–dimensional Lagrangian system along a path:
`(∂L/∂x) (t, q t, q̇ t)`. -/
