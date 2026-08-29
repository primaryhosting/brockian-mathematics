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

/-- The Gibbs entropy of a (finite) probability vector `p`, given by `-∑ pᵢ log pᵢ`. -/

lemma gibbsEntropy_eq_sum_negMulLog {n : ℕ} (p : Fin n → ℝ) :
    gibbsEntropy p = ∑ i, Real.negMulLog (p i) := by
  simp [gibbsEntropy, Real.negMulLog]

/-- The set of nonnegative vectors (containing the probability simplex) is convex. -/
