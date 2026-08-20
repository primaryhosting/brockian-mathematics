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

theorem szemeredi_of_le_two (k : ℕ) (hk : k ≤ 2) (A : Set ℕ) (hA : HasPositiveUpperDensity A) :
    HasAP A k :=
  furstenberg_szemeredi k (finitarySzemeredi_mono hk finitarySzemeredi_two) A hA

/-- Unconditional base case: a set of positive upper density contains a two-term
arithmetic progression. -/
