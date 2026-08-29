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

noncomputable def tailProd (M N : ℕ) : ℝ :=
  ∏ p ∈ (Finset.Ico (M + 1) (N + 1)).filter Nat.Prime, (1 - singularTerm p)

