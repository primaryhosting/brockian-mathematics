import Mathlib

/-!
# Assembly Window Constants
Category: A Assembly
Target: Zeta23Scaffold.assembly_window_constants
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Zeta23Scaffold

/-- The window function `H(λ) = 2 - 1/λ - λ/3`. -/

noncomputable def Hd (lam : Real) : Real := (1 + Hwin lam) / 2

/-- The window function `F(λ) = λ / (1 + λ² / 3)`. -/
