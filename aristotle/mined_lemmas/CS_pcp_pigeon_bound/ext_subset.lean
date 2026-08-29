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

lemma ext_subset (L : ℕ) (c : List Bool) (hc : c.length ≤ L) : ext L c ⊆ words L := by
  intro w hw
  simp only [ext, Finset.mem_image] at hw
  obtain ⟨u, hu, rfl⟩ := hw
  rw [mem_words] at hu ⊢
  simp [hu]
  omega

