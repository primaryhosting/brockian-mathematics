/-
# Cycle Fiedler Value
Category: Frontier Spectral
Target: Frontier.Spectral.cycle_fiedler_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the header above is
-- given as a plain block comment and repeated as a module docstring below.)

import Mathlib

/-!
# Cycle Fiedler Value
Category: Frontier Spectral
Target: Frontier.Spectral.cycle_fiedler_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Matrix SimpleGraph Complex ComplexConjugate

namespace Frontier.Spectral

/-! ## A discrete additive character on `ZMod N` -/

section Character

variable {N : ℕ}

/-- The primitive `N`-th root of unity `exp (2πi/N)`. -/

lemma two_ne_zero_zmod : (2 : ZMod (m + 3)) ≠ 0 := by
  have hv : ((2 : ℕ) : ZMod (m + 3)).val = 2 := ZMod.val_cast_of_lt (by omega)
  intro hc
  rw [show ((2 : ℕ) : ZMod (m + 3)) = (2 : ZMod (m + 3)) by push_cast; ring, hc] at hv
  simp at hv

