/-!
# Entropy Concave
Category: Chemistry
Target: Chem.entropy_concave
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Real Finset

/-- The probability simplex on a finite index type `ι`: vectors with nonnegative
entries summing to `1`. -/

def simplex (ι : Type*) [Fintype ι] : Set (ι → ℝ) :=
  {p | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1}

/-- The Gibbs entropy of a probability vector, `-∑ i, p i * log (p i)`. -/
