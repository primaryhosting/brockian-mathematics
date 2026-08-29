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

lemma singularPartial_mem_Icc (N : ℕ) : 0 ≤ singularPartial N ∧ singularPartial N ≤ 1 := by
  constructor
  · refine Finset.prod_nonneg ?_
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ico] at hp
    have := singularTerm_le_one hp.1.1
    linarith
  · refine Finset.prod_le_one ?_ ?_ <;> intro p hp
    · simp only [Finset.mem_filter, Finset.mem_Ico] at hp
      have := singularTerm_le_one hp.1.1
      linarith
    · have := singularTerm_nonneg p
      linarith

