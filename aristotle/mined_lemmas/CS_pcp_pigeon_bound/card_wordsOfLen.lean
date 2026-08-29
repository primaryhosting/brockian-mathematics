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

lemma card_wordsOfLen (n : ℕ) : (wordsOfLen n).card = 2 ^ n := by
  induction n with
  | zero => simp [wordsOfLen]
  | succ n ih =>
      classical
      have : (wordsOfLen (n + 1)) =
          Finset.univ.biUnion (fun b : Bool => (wordsOfLen n).image (b :: ·)) := rfl
      have hinj : ∀ b : Bool, Function.Injective (fun l : List Bool => b :: l) :=
        fun b x y h => by simpa using h
      rw [this, Finset.card_biUnion]
      · rw [Fintype.sum_bool, Finset.card_image_of_injective _ (hinj true),
          Finset.card_image_of_injective _ (hinj false), ih, pow_succ]
        ring
      · intro x _ y _ hxy
        simp only [Finset.disjoint_left, Finset.mem_image]
        rintro a ⟨l, -, rfl⟩ ⟨l', -, h⟩
        exact hxy ((List.cons_eq_cons.mp h).1).symm

/-- Words of length `n` extending a fixed prefix `w`. -/
