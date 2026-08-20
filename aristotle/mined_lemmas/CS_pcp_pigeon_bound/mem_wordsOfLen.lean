/-
# Pcp Pigeon Bound
Category: Computer Science
Target: CS.pcp_pigeon_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset

namespace CS

/-- The finite set of all binary words (lists of booleans) of length `n`. -/

@[simp] lemma mem_wordsOfLen {n : ℕ} {v : List Bool} : v ∈ wordsOfLen n ↔ v.length = n := by
  constructor
  · intro h
    simp only [wordsOfLen, Finset.mem_image, Finset.mem_univ, true_and] at h
    obtain ⟨f, rfl⟩ := h
    simp
  · intro h
    subst h
    simp only [wordsOfLen, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun i => v[i], by simp⟩

