/-
# Pcp Pigeon Bound
Category: Computer Science
Target: CS.pcp_pigeon_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace CS

/-- The finite set of all boolean lists of a given length. -/

lemma mem_boolLists {k : ℕ} {l : List Bool} : l ∈ boolLists k ↔ l.length = k := by
  constructor
  · rintro h
    simp only [boolLists, Finset.mem_image, Finset.mem_univ, true_and] at h
    obtain ⟨v, hv⟩ := h
    rw [← hv]
    exact v.2
  · intro h
    simp only [boolLists, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨l, h⟩, rfl⟩

