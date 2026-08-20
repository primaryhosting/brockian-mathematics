/-
# Pcp Pigeon Bound
Category: Computer Science
Target: CS.pcp_pigeon_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

open Finset

/-- The finite set of all binary strings of length `n`. -/

lemma mem_binWords {n : ℕ} {l : List Bool} : l ∈ binWords n ↔ l.length = n := by
  constructor
  · rintro h
    simp only [binWords, Finset.mem_image] at h
    obtain ⟨f, -, rfl⟩ := h
    simp
  · rintro rfl
    simp only [binWords, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun i => l[(i : ℕ)], List.ofFn_getElem l⟩

