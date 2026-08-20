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

theorem huffCost_achievable_aux : ∀ n : ℕ, ∀ W : Multiset ℝ, Multiset.card W = n →
    ∃ S : Multiset (ℝ × List Bool), S.map Prod.fst = W ∧
      PrefixFreeMultiset (S.map Prod.snd) ∧ codeCost S = huffCost W := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro W hcard
  by_cases hle : Multiset.card W ≤ 1
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hle with h | h
    · refine ⟨0, ?_, ⟨by simp, by simp⟩, ?_⟩
      · simp [Multiset.card_eq_zero.1 h]
      · simp [codeCost, Multiset.card_eq_zero.1 h]
    · obtain ⟨a, ha⟩ := Multiset.card_eq_one.1 h
      refine ⟨{(a, [])}, by simp [ha], ⟨by simp, ?_⟩, by simp [codeCost, ha]⟩
      intro u hu v hv hne
      simp at hu hv
      exact absurd (hu.trans hv.symm) hne
  · push_neg at hle
    have hWne : W ≠ 0 := by intro h; rw [h] at hle; simp at hle
    obtain ⟨x, hxW, hxmin⟩ := exists_min_of_ne_zero W hWne
    obtain ⟨W₁, hW₁⟩ := Multiset.exists_cons_of_mem hxW
    have hW₁ne : W₁ ≠ 0 := by
      intro h; rw [hW₁, h] at hle; simp at hle
    obtain ⟨y, hyW₁, hymin⟩ := exists_min_of_ne_zero W₁ hW₁ne
    obtain ⟨l, hl⟩ := Multiset.exists_cons_of_mem hyW₁
    have hWeq : W = x ::ₘ y ::ₘ l := by rw [hW₁, hl]
    have hxle : ∀ z ∈ l, x ≤ z := by
      intro z hz
      exact hxmin z (by rw [hWeq]; exact Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem hz))
    have hyle : ∀ z ∈ l, y ≤ z := by
      intro z hz
      exact hymin z (by rw [hl]; exact Multiset.mem_cons_of_mem hz)
    have hcard' : Multiset.card ((x + y) ::ₘ l) < n := by
      rw [← hcard, hWeq]; simp
    obtain ⟨S', hfst', hpf', hcost'⟩ := IH _ hcard' ((x + y) ::ₘ l) rfl
    have hmem : (x + y) ∈ S'.map Prod.fst := by rw [hfst']; exact Multiset.mem_cons_self _ _
    obtain ⟨p, hpS', hp⟩ := Multiset.mem_map.1 hmem
    obtain ⟨R, hR⟩ := Multiset.exists_cons_of_mem hpS'
    have hRfst : R.map Prod.fst = l := by
      have h2 : (x + y) ::ₘ R.map Prod.fst = (x + y) ::ₘ l := by
        rw [← hfst', hR]; simp [hp]
      exact (Multiset.cons_inj_right _).1 h2
    refine ⟨(x, p.2 ++ [false]) ::ₘ (y, p.2 ++ [true]) ::ₘ R, ?_, ?_, ?_⟩
    · simp only [Multiset.map_cons, hRfst]
      exact hWeq.symm
    · simp only [Multiset.map_cons]
      have hS'snd : S'.map Prod.snd = p.2 ::ₘ R.map Prod.snd := by rw [hR]; simp
      rw [hS'snd] at hpf'
      exact prefixFree_split p.2 (R.map Prod.snd) hpf'
    · have hcostS' : codeCost S' = (x + y) * (p.2.length : ℝ) + codeCost R := by
        rw [hR]; simp [codeCost, hp]
      have hhuff : huffCost W = (x + y) + huffCost ((x + y) ::ₘ l) := by
        rw [hWeq]; exact huffCost_cons_cons x y l hxle hyle
      simp only [codeCost, Multiset.map_cons, Multiset.sum_cons, List.length_append,
        List.length_singleton]
      rw [hhuff, ← hcost']
      simp only [codeCost] at hcostS' ⊢
      rw [hcostS']
      push_cast
      ring

/-! ## Turning a multiset solution into an indexed one -/

/-- If a multiset `S` maps onto the multiset of `g`-values of a finite index set, then `S`
can be indexed by that set compatibly with `g`. -/
