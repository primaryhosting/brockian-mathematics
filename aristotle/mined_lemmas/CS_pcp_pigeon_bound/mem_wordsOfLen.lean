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

@[simp] lemma mem_wordsOfLen {n : ℕ} {t : List Bool} :
    t ∈ wordsOfLen n ↔ t.length = n := by
  induction n generalizing t with
  | zero =>
      simp [wordsOfLen, List.length_eq_zero_iff]
  | succ n ih =>
      cases t with
      | nil => simp [wordsOfLen]
      | cons b t =>
          simp only [wordsOfLen, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_image,
            true_and, List.length_cons, ih, Nat.add_right_cancel_iff]
          constructor
          · rintro ⟨b', l, hl, h⟩
            simpa using (List.cons_eq_cons.mp h).2 ▸ hl
          · intro h
            exact ⟨b, t, h, rfl⟩

