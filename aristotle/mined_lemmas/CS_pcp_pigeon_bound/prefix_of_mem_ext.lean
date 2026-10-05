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

lemma prefix_of_mem_ext {L : ℕ} {c w : List Bool} (hw : w ∈ ext L c) : c <+: w := by
  simp only [ext, Finset.mem_image] at hw
  obtain ⟨u, _, rfl⟩ := hw
  exact List.prefix_append c u

/-- Kraft's inequality, natural-number form: for a prefix-free set `S` of binary
codewords, all of length at most `L`, we have `∑ 2 ^ (L - ℓ c) ≤ 2 ^ L`. -/
