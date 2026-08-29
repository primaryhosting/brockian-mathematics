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

lemma kraft_nat (S : Finset (List Bool)) (L : ℕ)
    (hL : ∀ c ∈ S, c.length ≤ L)
    (hpf : ∀ a ∈ S, ∀ b ∈ S, a <+: b → a = b) :
    ∑ c ∈ S, 2 ^ (L - c.length) ≤ 2 ^ L := by
  have hdisj : (S : Set (List Bool)).PairwiseDisjoint (ext L) := by
    intro a ha b hb hab
    simp only [Finset.mem_coe] at ha hb
    refine Finset.disjoint_left.mpr ?_
    intro w hwa hwb
    have h1 : a <+: w := prefix_of_mem_ext hwa
    have h2 : b <+: w := prefix_of_mem_ext hwb
    rcases List.prefix_or_prefix_of_prefix h1 h2 with h | h
    · exact hab (hpf a ha b hb h)
    · exact hab (hpf b hb a ha h).symm
  calc ∑ c ∈ S, 2 ^ (L - c.length)
      = ∑ c ∈ S, (ext L c).card := by
        exact Finset.sum_congr rfl fun c _ => (card_ext L c).symm
    _ = (S.biUnion (ext L)).card := (Finset.card_biUnion (fun a ha b hb hab =>
        hdisj (by simpa using ha) (by simpa using hb) hab)).symm
    _ ≤ (words L).card := Finset.card_le_card (by
        intro w hw
        simp only [Finset.mem_biUnion] at hw
        obtain ⟨c, hc, hwc⟩ := hw
        exact ext_subset L c (hL c hc) hwc)
    _ = 2 ^ L := card_words L

/-- **Kraft's inequality.** Any prefix-free binary code (a finite set `S` of codewords,
no one of which is a prefix of another) satisfies `∑ 2 ^ (-ℓ i) ≤ 1`. -/
