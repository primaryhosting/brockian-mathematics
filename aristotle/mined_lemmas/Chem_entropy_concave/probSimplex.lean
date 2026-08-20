import Mathlib

/-!
# Entropy Concave
Category: Chemistry
Target: Chem.entropy_concave
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Finset

variable {ι : Type*} [Fintype ι]

/-- The set of probability vectors indexed by `ι`. -/

def probSimplex (ι : Type*) [Fintype ι] : Set (ι → ℝ) :=
  {p | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1}

/-- The Gibbs entropy `-∑ i, p i * log (p i)` of a probability vector. -/
