import Mathlib

/-!
# Pcp Pigeon Bound
Category: Computer Science
Target: CS.pcp_pigeon_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace CS

/-- The finite set of all binary strings (lists of booleans) of length `n`. -/

lemma card_cube (n : ℕ) : (cube n).card = 2 ^ n := by
  induction n with
  | zero => simp [cube]
  | succ n ih =>
      have hinj : ∀ (b : Bool), Set.InjOn (List.cons b) (cube n : Set (List Bool)) := by
        intro b x _ y _ h
        simpa using h
      have hdisj : Disjoint ((cube n).image (List.cons false))
          ((cube n).image (List.cons true)) := by
        rw [Finset.disjoint_left]
        rintro u hu hu'
        simp only [Finset.mem_image] at hu hu'
        obtain ⟨x, _, rfl⟩ := hu
        obtain ⟨y, _, hy⟩ := hu'
        simp at hy
      rw [cube, Finset.card_union_of_disjoint hdisj,
        Finset.card_image_of_injOn (hinj false), Finset.card_image_of_injOn (hinj true), ih]
      ring

/-- **Kraft's inequality.** For any finite prefix-free binary code `S`
(i.e. no codeword is a prefix of another codeword), we have
`∑ w ∈ S, (1/2)^(length w) ≤ 1`. -/
