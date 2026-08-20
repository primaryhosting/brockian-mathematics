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

lemma card_wordsOfLen (n : ℕ) : (wordsOfLen n).card = 2 ^ n := by
  rw [wordsOfLen, Finset.card_image_of_injective _ List.ofFn_injective]
  simp

/-- The words of length `n` extending a fixed word `w` are exactly the words `w ++ u`
with `u` of length `n - w.length`. -/
