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

lemma sum_sq_pos {x : ZMod (m + 3) → ℝ} (hx : x ≠ 0) : 0 < ∑ i : ZMod (m + 3), (x i) ^ 2 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  have hle : (x i) ^ 2 ≤ ∑ j : ZMod (m + 3), (x j) ^ 2 :=
    Finset.single_le_sum (f := fun j : ZMod (m + 3) => (x j) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have : 0 < (x i) ^ 2 := pow_two_pos_of_ne_zero hi
  linarith

/-- The Fiedler value of the cycle, stated for the index type `ZMod (m+3)`. -/
