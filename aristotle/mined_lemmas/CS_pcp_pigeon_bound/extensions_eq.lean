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

lemma extensions_eq {n : ℕ} {w : List Bool} (hw : w.length ≤ n) :
    (wordsOfLen n).filter (fun v => w <+: v)
      = (wordsOfLen (n - w.length)).image (fun u => w ++ u) := by
  ext v
  simp only [Finset.mem_filter, mem_wordsOfLen, Finset.mem_image]
  constructor
  · rintro ⟨hlen, t, rfl⟩
    exact ⟨t, by simp at hlen ⊢; omega, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    refine ⟨by simp [hu]; omega, ⟨u, rfl⟩⟩

