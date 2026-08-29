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

lemma card_le_height {c : Finset α} {x : α} (hc : IsChain (· ≤ ·) (c : Set α))
    (hx : ∀ y ∈ c, y ≤ x) : c.card ≤ height x := by
  classical
  refine Finset.le_sup (f := Finset.card) ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hc, hx⟩

