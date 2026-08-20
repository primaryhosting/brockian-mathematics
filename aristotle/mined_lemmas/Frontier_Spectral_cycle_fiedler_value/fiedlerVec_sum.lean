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

lemma fiedlerVec_sum : ∑ j : ZMod (m + 3), fiedlerVec m j = 0 := by
  have h1 : ∑ j : ZMod (m + 3), chi (m + 3) j = 0 := by
    have h := sum_chi (N := m + 3) 1
    simp only [one_mul, if_neg one_ne_zero_zmod] at h
    exact h
  have h2 : ∑ j : ZMod (m + 3), fiedlerVec m j = (∑ j : ZMod (m + 3), chi (m + 3) j).re := by
    simp [fiedlerVec, Complex.re_sum]
  rw [h2, h1, Complex.zero_re]

