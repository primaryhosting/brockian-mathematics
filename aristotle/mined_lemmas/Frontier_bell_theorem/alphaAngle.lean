/-!
# Bell Theorem
Category: Frontier Physics
Target: Frontier.bell_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

open Finset

/-- The CHSH combination of four correlation values. -/

noncomputable def alphaAngle : Bool → ℝ := fun i => if i then Real.pi / 2 else 0

/-- Bob's two measurement angles in the quantum (singlet) setup. -/
