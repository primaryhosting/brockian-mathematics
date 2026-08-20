import Mathlib

/-!
# Le Chatelier Sign
Category: Chemistry
Target: Chem.leChatelier_sign
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace Chem

/-- The van 't Hoff equilibrium constant as a function of absolute temperature `T`:
`K T = A * exp (-ΔH / (R * T))`, obtained by integrating the van 't Hoff equation
`d (log K) / dT = ΔH / (R * T ^ 2)` with `ΔH` and `R` constant. -/

noncomputable def K (A R dH T : ℝ) : ℝ := A * Real.exp (-dH / (R * T))

/-- **Le Chatelier sign (van 't Hoff).** For an exothermic reaction (`ΔH < 0`), with positive
pre-exponential factor `A` and positive gas constant `R`, the equilibrium constant
`K T = A * exp (-ΔH / (R * T))` is strictly decreasing in the absolute temperature `T > 0`. -/
