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

lemma sum_shift_sub {α : Type*} [AddCommMonoid α] (f : ZMod (m + 3) → α) :
    ∑ i : ZMod (m + 3), f (i - 1) = ∑ i : ZMod (m + 3), f i :=
  Fintype.sum_equiv (Equiv.subRight (1 : ZMod (m + 3))) _ _ (fun _ => rfl)

