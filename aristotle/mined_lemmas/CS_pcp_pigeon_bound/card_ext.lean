import Mathlib
/-!
# Pcp Pigeon Bound
Category: Computer Science
Target: CS.pcp_pigeon_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- The finset of all boolean words (lists) of length `n`. -/

lemma card_ext (L : ℕ) (c : List Bool) : (ext L c).card = 2 ^ (L - c.length) := by
  rw [ext, Finset.card_image_of_injective _ (List.append_right_injective c), card_words]

