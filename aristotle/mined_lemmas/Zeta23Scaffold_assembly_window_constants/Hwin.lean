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

noncomputable def Hwin (lam : Real) : Real := 2 - 1 / lam - lam / 3

/-- The derived window function `H_d(λ) = (1 + H(λ)) / 2`. -/
