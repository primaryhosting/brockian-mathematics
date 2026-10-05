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

lemma card_le_maxChainLen {c : Finset α} (hc : IsChain (· ≤ ·) (c : Set α)) :
    c.card ≤ maxChainLen α := by
  classical
  exact Finset.le_sup (f := Finset.card) (by simpa [maxChainLen] using hc)

