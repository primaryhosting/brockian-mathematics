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

lemma singularPartial_three : singularPartial 3 = 3 / 4 := by
  have hIco : (Finset.Ico 3 (3 + 1)).filter Nat.Prime = {3} := by decide
  unfold singularPartial
  rw [hIco]
  norm_num [singularTerm]

/-- The truncation at level `4` also equals `3/4`, since `4` is not prime. -/
