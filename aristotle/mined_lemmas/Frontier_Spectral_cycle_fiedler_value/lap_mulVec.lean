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

lemma lap_mulVec (x : ZMod (m + 3) → ℝ) (i : ZMod (m + 3)) :
    ((cycleGraph (m + 3)).lapMatrix ℝ *ᵥ x) i = 2 * x i - x (i - 1) - x (i + 1) := by
  have hne : (i - 1 : ZMod (m + 3)) ≠ i + 1 := fun h =>
    two_ne_zero_zmod (by linear_combination -h)
  rw [SimpleGraph.lapMatrix_mulVec_apply]
  have hdeg : (cycleGraph (m + 3)).degree i = 2 := cycleGraph_degree_three_le
  have hnb : (cycleGraph (m + 3)).neighborFinset i = {i - 1, i + 1} := cycleGraph_neighborFinset
  have hs : ∑ u ∈ ({i - 1, i + 1} : Finset (Fin (m + 3))), x u = x (i - 1) + x (i + 1) :=
    Finset.sum_pair hne
  rw [hdeg, hnb, hs]
  push_cast
  ring

