import RequestProject.HuffmanKraft

/-!
# Weighted depth multisets, the Huffman merging process, and the optimality bound
-/

namespace CS

/-- A *weighted depth multiset*: a finite multiset of pairs `(weight, codeword length)`. -/
abbrev WD := Multiset (ℝ × ℕ)

/-- The expected codeword length associated to a weighted depth multiset. -/

theorem two_le_count_max {D : WD} {M : ℕ} (hmax : ∀ p ∈ D, p.2 ≤ M) (hM : 1 ≤ M)
    (hk : kraft D = 1) (hex : ∃ p ∈ D, p.2 = M) :
    2 ≤ D.countP (fun p => p.2 = M) := by
  classical
  obtain ⟨t, ht⟩ := kn_parity M D hmax
  have h1 : kraft D * 2 ^ M = (kn M D : ℝ) := kraft_eq_kn M D hmax
  rw [hk, one_mul] at h1
  have h2 : kn M D = 2 ^ M := by exact_mod_cast h1.symm
  have hpos : 0 < D.countP (fun p => p.2 = M) := by
    obtain ⟨p, hp, hpM⟩ := hex
    rw [Multiset.countP_pos]; exact ⟨p, hp, hpM⟩
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
  have hdvd : 2 ∣ kn (k + 1) D := ⟨2 ^ k, by rw [h2, pow_succ]; ring⟩
  omega

/-- Any weighted depth multiset with Kraft sum `≤ 1` can be replaced by one with the same
weights, Kraft sum exactly `1`, and no larger cost. -/
