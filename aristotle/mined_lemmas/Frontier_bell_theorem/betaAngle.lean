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

noncomputable def betaAngle : Bool → ℝ := fun j => if j then -(Real.pi / 4) else Real.pi / 4

/-- The quantum correlation predicted for two spin measurements at the given angles. -/
