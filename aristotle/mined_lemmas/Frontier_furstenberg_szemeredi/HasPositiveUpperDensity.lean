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

def HasPositiveUpperDensity (A : Set ℕ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ M : ℕ, ∃ N ≥ M, δ * N ≤ (countBelow A N : ℝ)

/-- `A` contains an arithmetic progression of length `k` (with positive common difference). -/
