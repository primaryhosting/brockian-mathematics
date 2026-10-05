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

lemma filter_prefix_eq_image {n : ℕ} {w : List Bool} (hw : w.length ≤ n) :
    (wordsOfLen n).filter (fun t => w <+: t) =
      (wordsOfLen (n - w.length)).image (fun s => w ++ s) := by
  classical
  ext t
  simp only [Finset.mem_filter, Finset.mem_image, mem_wordsOfLen]
  constructor
  · rintro ⟨hlen, s, rfl⟩
    exact ⟨s, by simp at hlen ⊢; omega, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨by simp [hs]; omega, ⟨s, rfl⟩⟩

