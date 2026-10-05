import Mathlib

/-!
# Pcp Pigeon Bound
Category: Computer Science
Target: CS.pcp_pigeon_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- The finset of all binary words of a given length. -/

lemma card_filter_prefix {n : ℕ} {w : List Bool} (hw : w.length ≤ n) :
    ((wordsOfLen n).filter (fun t => w <+: t)).card = 2 ^ (n - w.length) := by
  classical
  rw [filter_prefix_eq_image hw,
    Finset.card_image_of_injective _ (fun x y h => List.append_cancel_left h),
    card_wordsOfLen]

/-- Counting form of Kraft's inequality: for a prefix-free finite set of binary words all of
length at most `n`, the number of length-`n` extensions is at most `2 ^ n`. -/
