import RequestProject.Huffman

/-!
# Achievability of the Huffman cost

Companion to `RequestProject.Huffman`.  Here we show that the Huffman cost is *attained*:
there really is a prefix code whose expected codeword length equals `CS.huffCost`.

Combined with the optimality bound `CS.huffman_optimal`, this gives
`CS.huffman_isLeast`: the Huffman cost is the least expected codeword length among all
prefix codes.
-/

namespace CS

open scoped BigOperators

noncomputable section

/-- A multiset of binary codewords is prefix-free: the codewords are pairwise distinct and
none is a prefix of another. -/

theorem exists_min_at_max_length (S : Multiset (ℝ × ℕ)) (d : ℕ) (x : ℝ)
    (hd : ∃ p ∈ S, p.2 = d) (hxmem : ∃ q ∈ S, q.1 = x)
    (hxmin : ∀ p ∈ S, x ≤ p.1) (hdmax : ∀ p ∈ S, p.2 ≤ d) :
    ∃ R : Multiset (ℝ × ℕ), S.map Prod.fst = ((x, d) ::ₘ R).map Prod.fst ∧
      S.map Prod.snd = ((x, d) ::ₘ R).map Prod.snd ∧
      costOf ((x, d) ::ₘ R) ≤ costOf S := by
  obtain ⟨p, hpS, hpd⟩ := hd
  obtain ⟨R₀, hR₀⟩ := Multiset.exists_cons_of_mem hpS
  by_cases hpx : p.1 = x
  · have hp : ((x, d) : ℝ × ℕ) = p := Prod.ext hpx.symm hpd.symm
    exact ⟨R₀, by rw [hR₀, hp], by rw [hR₀, hp], by rw [hR₀, hp]⟩
  · obtain ⟨q, hqS, hqx⟩ := hxmem
    have hqR : q ∈ R₀ := by
      have : q ∈ p ::ₘ R₀ := hR₀ ▸ hqS
      rcases Multiset.mem_cons.1 this with rfl | h
      · exact absurd hqx hpx
      · exact h
    obtain ⟨R, hR⟩ := Multiset.exists_cons_of_mem hqR
    refine ⟨(p.1, q.2) ::ₘ R, ?_, ?_, ?_⟩
    · rw [hR₀, hR]
      simp only [Multiset.map_cons]
      rw [← hqx]
      exact Multiset.cons_swap _ _ _
    · rw [hR₀, hR]
      simp only [Multiset.map_cons]
      rw [← hpd]
    · rw [hR₀, hR]
      simp only [costOf_cons]
      have h1 : x ≤ p.1 := hxmin p hpS
      have h2 : (q.2 : ℝ) ≤ (d : ℝ) := by
        exact_mod_cast hdmax q hqS
      have hqp : q.1 = x := hqx
      rw [hqp, hpd]
      nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)]

/-! ## Kraft bookkeeping -/

/-- Integer version of the Kraft sum, scaled by `2 ^ d`. -/
