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

noncomputable def Fwin (lam : Real) : Real := lam / (1 + lam ^ 2 / 3)

/-- Window-constant assembly identities of preprint eq. (1.3):
`H(1) = 2/3`, `H_d(1) = 5/6`, `F(1) = 3/4`, and `2·F(1) - 1 = 1/2`. -/
