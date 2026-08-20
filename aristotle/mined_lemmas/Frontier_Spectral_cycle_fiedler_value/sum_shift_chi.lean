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

lemma sum_shift_chi [NeZero N] (f : ZMod N → ℂ) (k : ZMod N) :
    ∑ j : ZMod N, f (j + 1) * chi N (j * k)
      = chi N (-k) * ∑ j : ZMod N, f j * chi N (j * k) := by
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.addRight (1 : ZMod N)) _ _ (fun j => ?_)
  simp only [Equiv.coe_addRight]
  rw [show chi N (-k) * (f (j + 1) * chi N ((j + 1) * k))
      = f (j + 1) * (chi N (-k) * chi N ((j + 1) * k)) by ring, ← chi_add]
  congr 2
  ring

end Character

/-! ## An elementary bound on cosines -/

