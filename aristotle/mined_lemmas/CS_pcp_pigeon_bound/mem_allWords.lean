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

lemma mem_allWords {n : ℕ} {w : List Bool} : w ∈ allWords n ↔ w.length = n := by
  constructor
  · rintro hw
    simp only [allWords, Finset.mem_image, Finset.mem_univ, true_and] at hw
    obtain ⟨f, rfl⟩ := hw
    simp
  · intro hw
    subst hw
    simp only [allWords, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun i => w[i], List.ofFn_getElem w⟩

