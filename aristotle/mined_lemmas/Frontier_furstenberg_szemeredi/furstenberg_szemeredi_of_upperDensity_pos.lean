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

theorem furstenberg_szemeredi_of_upperDensity_pos (k : ℕ) (hfin : FinitarySzemeredi k)
    (A : Set ℕ) (hA : 0 < upperDensity A) : HasAP A k :=
  furstenberg_szemeredi k hfin A (hasPositiveUpperDensity_of_upperDensity_pos hA)

/-- The multiple-recurrence formulation is equivalent to the existence of progressions. -/
