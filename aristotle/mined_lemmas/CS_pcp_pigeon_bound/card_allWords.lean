/-
# Pcp Pigeon Bound
Category: Computer Science
Target: CS.pcp_pigeon_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pcp Pigeon Bound
Category: Computer Science
Target: CS.pcp_pigeon_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- The finite set of all binary words of length `n`. -/

lemma card_allWords (n : ℕ) : (allWords n).card = 2 ^ n := by
  rw [allWords, Finset.card_image_of_injective _ List.ofFn_injective, Finset.card_univ]
  simp

/-- Kraft's inequality, in the natural-number form: for a prefix-free set `S` of binary
codewords with maximal length `L`, we have `∑ 2 ^ (L - ℓ i) ≤ 2 ^ L`. -/
