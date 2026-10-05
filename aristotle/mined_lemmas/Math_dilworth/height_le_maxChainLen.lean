/-
# Dilworth
Category: Pure Mathematics
Target: Math.dilworth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset

namespace Math

open scoped Classical in
/-- The maximal cardinality of a chain in a finite partial order. -/

lemma height_le_maxChainLen (x : α) : height x ≤ maxChainLen α := by
  classical
  refine Finset.sup_le ?_
  intro c hc
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
  exact card_le_maxChainLen hc.1

