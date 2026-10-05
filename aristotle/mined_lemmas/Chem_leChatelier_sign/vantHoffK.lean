/-
# Le Chatelier Sign
Category: Chemistry
Target: Chem.leChatelier_sign
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

/-- The van 't Hoff equilibrium constant: `ln K(T) = C - ΔH / (R T)`, i.e.
`K(T) = exp (C - ΔH / (R * T))`, where `ΔH` is the reaction enthalpy, `R > 0` the
gas constant and `C` an integration constant. -/

noncomputable def vantHoffK (R C ΔH T : ℝ) : ℝ := Real.exp (C - ΔH / (R * T))

/-- Van 't Hoff equation: `d/dT (log (K T)) = ΔH / (R T ^ 2)`. -/
