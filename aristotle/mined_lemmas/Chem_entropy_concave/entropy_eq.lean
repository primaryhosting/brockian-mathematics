/-
# Entropy Concave
Category: Chemistry
Target: Chem.entropy_concave
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Real Finset

/-- The Gibbs entropy of a (finite) probability vector `p`: `S(p) = -∑ i, p i * log (p i)`,
written using Mathlib's `Real.negMulLog x = -x * log x` (so that the `p i = 0` terms vanish). -/

lemma entropy_eq {n : ℕ} (p : Fin n → ℝ) : entropy p = -∑ i, p i * Real.log (p i) := by
  simp [entropy, Real.negMulLog, Finset.sum_neg_distrib]

/-- **Gibbs entropy is concave**: `p ↦ -∑ i, p i * log (p i)` is a concave function on the set of
nonnegative vectors (in particular on the probability simplex).

The one–dimensional ingredient is `Real.concaveOn_negMulLog : ConcaveOn ℝ (Set.Ici 0) negMulLog`;
concavity of the sum follows termwise. -/
