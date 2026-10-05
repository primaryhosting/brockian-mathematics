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

lemma height_pos (x : α) : 0 < height x := by
  have h : ({x} : Finset α).card ≤ height x := by
    refine card_le_height ?_ ?_
    · simp
    · simp
  simpa using h

