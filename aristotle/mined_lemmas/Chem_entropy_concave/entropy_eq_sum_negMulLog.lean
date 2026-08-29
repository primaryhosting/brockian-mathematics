/-
# Entropy Concave
Category: Chemistry
Target: Chem.entropy_concave
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators

namespace Chem

/-- The Gibbs (Shannon) entropy of a probability vector `p : ι → ℝ`,
namely `-∑ i, p i * log (p i)`. -/

lemma entropy_eq_sum_negMulLog {ι : Type*} [Fintype ι] (p : ι → ℝ) :
    entropy p = ∑ i, Real.negMulLog (p i) := by
  simp [entropy, Real.negMulLog, Finset.sum_neg_distrib]

/-- **Concavity of the Gibbs entropy.** The map `p ↦ -∑ i, p i * log (p i)` is concave
on the standard simplex of probability vectors.

The key ingredient is `Real.concaveOn_negMulLog`, the concavity of `x ↦ -x * log x`
on `[0, ∞)`. -/
