/-
# Singular Series Convergence Rate
Category: Brockian Corpus
Target: Brockian.SingularSeriesConvergenceRate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Filter Topology

namespace Brockian

/-- The local factor deficiency `1/(p-1)^2` occurring in the twin-prime singular series. -/

lemma singularPartial_four : singularPartial 4 = 3 / 4 := by
  have hIco : (Finset.Ico 3 (4 + 1)).filter Nat.Prime = {3} := by decide
  unfold singularPartial
  rw [hIco]
  norm_num [singularTerm]

/-- Every truncation, hence the limit, is at least `1/2`; in particular the singular
series does not degenerate to `0`. -/
