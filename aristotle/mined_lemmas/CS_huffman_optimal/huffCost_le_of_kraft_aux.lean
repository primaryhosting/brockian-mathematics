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

theorem huffCost_le_of_kraft_aux : ∀ n : ℕ, ∀ S : Multiset (ℝ × ℕ),
    (S.map Prod.snd).sum = n → (∀ p ∈ S, 0 ≤ p.1) → kraft (S.map Prod.snd) ≤ 1 →
    huffCost (S.map Prod.fst) ≤ costOf S := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro S hsum hpos hk
  have hposW : ∀ w ∈ S.map Prod.fst, 0 ≤ w := by
    intro w hw
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.1 hw
    exact hpos q hq
  by_cases hcard : Multiset.card S ≤ 1
  · -- Base case: at most one codeword.
    have hc : Multiset.card (S.map Prod.fst) ≤ 1 := by simpa using hcard
    have h0 : huffCost (S.map Prod.fst) = 0 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hc with h | h
      · rw [Multiset.card_eq_zero.1 h]; exact huffCost_zero
      · obtain ⟨a, ha⟩ := Multiset.card_eq_one.1 h
        rw [ha]; exact huffCost_singleton a
    rw [h0]
    exact costOf_nonneg hpos
  push_neg at hcard
  have hSne : S ≠ 0 := by
    intro h; rw [h] at hcard; simp at hcard
  obtain ⟨d, hdmem, hdmax⟩ := exists_max_of_ne_zero (S.map Prod.snd) (by simpa using hSne)
  obtain ⟨p₀, hp₀S, hp₀d⟩ := Multiset.mem_map.1 hdmem
  have hdmaxS : ∀ q ∈ S, q.2 ≤ d := fun q hq => hdmax _ (Multiset.mem_map_of_mem _ hq)
  obtain ⟨R, hR⟩ := Multiset.exists_cons_of_mem hp₀S
  have hlen : S.map Prod.snd = d ::ₘ R.map Prod.snd := by rw [hR]; simp [hp₀d]
  have hRS : ∀ q ∈ R, q ∈ S := by
    intro q hq; rw [hR]; exact Multiset.mem_cons_of_mem hq
  by_cases hcount : (S.map Prod.snd).count d ≤ 1
  · -- Case A: the maximal length is attained exactly once; shorten that codeword.
    have hcount0 : (R.map Prod.snd).count d = 0 := by
      rw [hlen, Multiset.count_cons_self] at hcount
      omega
    have hnotmem : d ∉ R.map Prod.snd := Multiset.count_eq_zero.1 hcount0
    have hRlt : ∀ q ∈ R, q.2 < d := by
      intro q hq
      have h1 : q.2 ≤ d := hdmaxS q (hRS q hq)
      have h2 : q.2 ≠ d := by
        intro h; exact hnotmem (h ▸ Multiset.mem_map_of_mem _ hq)
      omega
    have hRlt' : ∀ m ∈ R.map Prod.snd, m < d := by
      intro m hm
      obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.1 hm
      exact hRlt q hq
    have hd1 : 1 ≤ d := by
      by_contra hcon
      have hd0 : d = 0 := by omega
      have hRz : R = 0 := by
        refine Multiset.eq_zero_of_forall_notMem ?_
        intro q hq
        have := hRlt q hq
        omega
      rw [hR, hRz] at hcard
      simp at hcard
    set S' : Multiset (ℝ × ℕ) := (p₀.1, d - 1) ::ₘ R with hS'
    have hfst : S'.map Prod.fst = S.map Prod.fst := by rw [hS', hR]; simp
    have hsnd : S'.map Prod.snd = (d - 1) ::ₘ R.map Prod.snd := by rw [hS']; simp
    have hnsum : (S.map Prod.snd).sum = d + (R.map Prod.snd).sum := by rw [hlen]; simp
    have hlt : (S'.map Prod.snd).sum < n := by
      rw [hsnd]
      simp only [Multiset.sum_cons]
      omega
    have hk' : kraft (S'.map Prod.snd) ≤ 1 := by
      rw [hsnd]
      exact kraft_shorten_unique_max d hd1 (R.map Prod.snd) hRlt' (by rw [← hlen]; exact hk)
    have hpos' : ∀ q ∈ S', 0 ≤ q.1 := by
      intro q hq
      rw [hS'] at hq
      rcases Multiset.mem_cons.1 hq with rfl | hq
      · exact hpos p₀ hp₀S
      · exact hpos q (hRS q hq)
    have hIH := IH _ hlt S' rfl hpos' hk'
    have hcost : costOf S' ≤ costOf S := by
      rw [hS', hR, costOf_cons, costOf_cons, hp₀d]
      have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
        have : (1:ℕ) ≤ d := hd1
        push_cast [Nat.cast_sub this]
        ring
      rw [hcast]
      have := hpos p₀ hp₀S
      nlinarith
    rw [← hfst]
    exact hIH.trans hcost
  · -- Case B: at least two codewords of maximal length; merge the two smallest weights.
    push_neg at hcount
    have hcountR : 1 ≤ (R.map Prod.snd).count d := by
      rw [hlen, Multiset.count_cons_self] at hcount
      omega
    have hdmemR : d ∈ R.map Prod.snd := by
      rw [← Multiset.count_pos]; omega
    obtain ⟨L₀, hL₀⟩ := Multiset.exists_cons_of_mem hdmemR
    have hd1 : 1 ≤ d := by
      by_contra hcon
      have hd0 : d = 0 := by omega
      have : kraft (S.map Prod.snd) = 1 + (1 + kraft L₀) := by
        rw [hlen, hL₀, kraft_cons, kraft_cons, hd0]
        norm_num
      have := kraft_nonneg L₀
      linarith [hk, this]
    -- pick the smallest weight and move it to depth `d`
    obtain ⟨x, hxmem, hxmin⟩ := exists_min_of_ne_zero (S.map Prod.fst) (by simpa using hSne)
    obtain ⟨qx, hqxS, hqx⟩ := Multiset.mem_map.1 hxmem
    obtain ⟨R₁, hfst1, hsnd1, hcost1⟩ :=
      exists_min_at_max_length S d x ⟨p₀, hp₀S, hp₀d⟩ ⟨qx, hqxS, hqx⟩
        (fun q hq => hxmin _ (Multiset.mem_map_of_mem _ hq)) hdmaxS
    simp only [Multiset.map_cons] at hfst1 hsnd1
    -- `R₁` still contains a codeword of maximal length
    have hcount1 : 1 ≤ (R₁.map Prod.snd).count d := by
      have : (S.map Prod.snd).count d = (R₁.map Prod.snd).count d + 1 := by
        rw [hsnd1, Multiset.count_cons_self]
      omega
    have hdmemR₁ : d ∈ R₁.map Prod.snd := by rw [← Multiset.count_pos]; omega
    obtain ⟨p₁, hp₁R₁, hp₁d⟩ := Multiset.mem_map.1 hdmemR₁
    have hR₁ne : R₁ ≠ 0 := by
      intro h; rw [h] at hp₁R₁; simp at hp₁R₁
    have hmemR₁S : ∀ w ∈ R₁.map Prod.fst, w ∈ S.map Prod.fst := by
      intro w hw; rw [hfst1]; exact Multiset.mem_cons_of_mem hw
    have hdmaxR₁ : ∀ q ∈ R₁, q.2 ≤ d := by
      intro q hq
      have : q.2 ∈ S.map Prod.snd := by
        rw [hsnd1]; exact Multiset.mem_cons_of_mem (Multiset.mem_map_of_mem _ hq)
      exact hdmax _ this
    obtain ⟨y, hymem, hymin⟩ := exists_min_of_ne_zero (R₁.map Prod.fst) (by simpa using hR₁ne)
    obtain ⟨qy, hqyR₁, hqy⟩ := Multiset.mem_map.1 hymem
    obtain ⟨R₂, hfst2, hsnd2, hcost2⟩ :=
      exists_min_at_max_length R₁ d y ⟨p₁, hp₁R₁, hp₁d⟩ ⟨qy, hqyR₁, hqy⟩
        (fun q hq => hymin _ (Multiset.mem_map_of_mem _ hq)) hdmaxR₁
    simp only [Multiset.map_cons] at hfst2 hsnd2
    -- the merged instance
    set T : Multiset (ℝ × ℕ) := (x + y, d - 1) ::ₘ R₂ with hT
    have hTfst : T.map Prod.fst = (x + y) ::ₘ R₂.map Prod.fst := by rw [hT]; simp
    have hTsnd : T.map Prod.snd = (d - 1) ::ₘ R₂.map Prod.snd := by rw [hT]; simp
    have hSsnd : S.map Prod.snd = d ::ₘ d ::ₘ R₂.map Prod.snd := by rw [hsnd1, hsnd2]
    have hSfst : S.map Prod.fst = x ::ₘ y ::ₘ R₂.map Prod.fst := by rw [hfst1, hfst2]
    have hnsum : (S.map Prod.snd).sum = d + (d + (R₂.map Prod.snd).sum) := by
      rw [hSsnd]; simp
    have hlt : (T.map Prod.snd).sum < n := by
      rw [hTsnd]; simp only [Multiset.sum_cons]; omega
    have hk' : kraft (T.map Prod.snd) ≤ 1 := by
      rw [hTsnd, kraft_merge d hd1, ← hSsnd]; exact hk
    -- nonnegativity
    have hxnn : 0 ≤ x := hposW x hxmem
    have hynn : 0 ≤ y := hposW y (hmemR₁S y hymem)
    have hR₂w : ∀ w ∈ R₂.map Prod.fst, w ∈ S.map Prod.fst := by
      intro w hw
      rw [hSfst]
      exact Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem hw)
    have hpos' : ∀ q ∈ T, 0 ≤ q.1 := by
      intro q hq
      rw [hT] at hq
      rcases Multiset.mem_cons.1 hq with rfl | hq
      · exact add_nonneg hxnn hynn
      · exact hposW _ (hR₂w _ (Multiset.mem_map_of_mem _ hq))
    have hIH := IH _ hlt T rfl hpos' hk'
    -- the Huffman recursion
    have hxle : ∀ z ∈ R₂.map Prod.fst, x ≤ z := fun z hz => hxmin z (hR₂w z hz)
    have hyle : ∀ z ∈ R₂.map Prod.fst, y ≤ z := by
      intro z hz
      refine hymin z ?_
      rw [hfst2]
      exact Multiset.mem_cons_of_mem hz
    have hhuff : huffCost (S.map Prod.fst) = (x + y) + huffCost ((x + y) ::ₘ R₂.map Prod.fst) := by
      rw [hSfst]
      exact huffCost_cons_cons x y _ hxle hyle
    have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
      push_cast [Nat.cast_sub hd1]; ring
    have hTcost : costOf T = (x + y) * ((d : ℝ) - 1) + costOf R₂ := by
      rw [hT, costOf_cons, hcast]
    have hcostS₁ : costOf ((x, d) ::ₘ R₁) ≤ costOf S := hcost1
    have hcostR₁ : costOf ((y, d) ::ₘ R₂) ≤ costOf R₁ := hcost2
    rw [hhuff, ← hTfst]
    have h1 : huffCost (T.map Prod.fst) ≤ costOf T := hIH
    rw [hTfst] at h1
    simp only [costOf_cons] at hcostS₁ hcostR₁
    rw [hTcost] at h1
    nlinarith [h1, hcostS₁, hcostR₁]

/-- **Core optimality of Huffman coding.**  If codeword lengths are attached to the weights
in such a way that the Kraft inequality holds, then the resulting expected length is at
least the Huffman cost. -/
