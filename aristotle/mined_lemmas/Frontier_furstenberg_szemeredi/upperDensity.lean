/- (Lean requires `import` to precede any module docstring, so the header below is a
plain block comment; it is repeated verbatim as a module docstring after the import.)
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Finset

namespace Frontier

noncomputable section

open Classical in
/-- The number of elements of `A` below `N`. -/

def upperDensity (A : Set ℕ) : ℝ :=
  limsup (fun N : ℕ => (countBelow A N : ℝ) / N) atTop

/-- `A` has positive upper density: for some `δ > 0`, the counting function of `A`
exceeds `δ N` for infinitely many `N`.  This is exactly `upperDensity A > 0`
(see `hasPositiveUpperDensity_of_upperDensity_pos`). -/
