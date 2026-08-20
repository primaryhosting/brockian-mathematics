/-
# Psi Cubic Eq One Of Small
Category: A Assembly
Target: Zeta23Scaffold.psiCubic_eq_one_of_small
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Zeta23Scaffold

/-- The cubic weight `psi(m) = m/2 + (2m^2 - m^3)/18 + (4/9)·[m = 1]`. -/

def psiCubic (m : Nat) : Rat :=
  (m : Rat) / 2 + (2 * (m : Rat) ^ 2 - (m : Rat) ^ 3) / 18 + (if m = 1 then 4 / 9 else 0)

/-- The cubic weight attains the value `1` at `m = 1, 2, 3`. -/
