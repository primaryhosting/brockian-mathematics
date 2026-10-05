import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


theorem buildList_optimal (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) :
    ∀ (n : ℕ) (ts : List (HTree α)), ts.length = n → ts ≠ [] →
      ∀ (M : Multiset (HTree α × ℕ)), M.map Prod.fst = (↑ts : Multiset (HTree α)) →
        kraftL (klen M) ≤ 1 →
        listCost w (buildList w ts) ≤ gcost (HTree.cost w) (HTree.wt w) M := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ts hlen hne M hM hK
    by_cases hbig : 2 ≤ ts.length
    · -- inductive step
      obtain ⟨t1, t2, rest, hcs, hmul, hw12, hmin, hrl⟩ := combineStep_spec w ts hbig
      rw [hmul] at hM
      obtain ⟨a, M1, hM1, hM1f⟩ := exists_pair_of_map_fst hM
      obtain ⟨b, N, hN, hNf⟩ := exists_pair_of_map_fst hM1f
      subst hM1
      subst hN
      have hNW : ∀ p ∈ N, t2.wt w ≤ p.1.wt w := by
        intro p hp
        have : p.1 ∈ N.map Prod.fst := Multiset.mem_map_of_mem _ hp
        rw [hNf] at this
        exact hmin p.1 (by simpa using this)
      obtain ⟨c, N', hN'f, hc1, hK', hcost'⟩ :=
        normalize (HTree.cost w) (HTree.wt w) t1 t2 hw12 (wt_nonneg hw t1) N hNW a b hK
      -- the merged assignment
      set Mstar : Multiset (HTree α × ℕ) := (HTree.node t1 t2, c - 1) ::ₘ N' with hMstar
      have hcast : ((c - 1 : ℕ) : ℝ) = (c : ℝ) - 1 := by
        have : (1:ℕ) ≤ c := hc1
        push_cast [Nat.cast_sub this]
        ring
      have hKstar : kraftL (klen Mstar) ≤ 1 := by
        have hz : ((c - 1 : ℕ) : ℤ) = (c : ℤ) - 1 := by omega
        have h2 : (2:ℝ) ^ (-((c - 1 : ℕ) : ℤ)) = 2 * 2 ^ (-(c : ℤ)) := by
          rw [hz]
          rw [neg_sub, sub_eq_add_neg, zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
          ring
        simp only [hMstar, klen_cons, kraftL_cons] at *
        rw [h2]
        linarith
      have hMstarf : Mstar.map Prod.fst = (↑(combineStep w ts) : Multiset (HTree α)) := by
        rw [hcs, hMstar]
        simp [hN'f, hNf]
      have hgc : gcost (HTree.cost w) (HTree.wt w) Mstar
          = gcost (HTree.cost w) (HTree.wt w) ((t1, c) ::ₘ (t2, c) ::ₘ N') := by
        simp only [hMstar, gcost_cons, cost_node, wt_node, hcast]
        ring
      have hlt : (combineStep w ts).length < n := by
        have := combineStep_length w ts hbig
        omega
      have hne' : combineStep w ts ≠ [] := by rw [hcs]; simp
      have := ih (combineStep w ts).length hlt (combineStep w ts) rfl hne' Mstar hMstarf hKstar
      rw [buildList_of_le w hbig]
      calc listCost w (buildList w (combineStep w ts))
          ≤ gcost (HTree.cost w) (HTree.wt w) Mstar := this
        _ = gcost (HTree.cost w) (HTree.wt w) ((t1, c) ::ₘ (t2, c) ::ₘ N') := hgc
        _ ≤ _ := hcost'
    · -- base case: a single tree
      push_neg at hbig
      rw [buildList_of_lt w hbig]
      obtain ⟨t, hts⟩ : ∃ t, ts = [t] := by
        match ts, hne, hbig with
        | [t], _, _ => exact ⟨t, rfl⟩
      subst hts
      have hcard : Multiset.card M = 1 := by
        have := congrArg Multiset.card hM
        simpa using this
      obtain ⟨p, hp⟩ := Multiset.card_eq_one.1 hcard
      subst hp
      have hp1 : p.1 = t := by
        have := hM
        simp at this
        exact this
      simp only [listCost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        gcost, Multiset.map_singleton, Multiset.sum_singleton, hp1]
      have : 0 ≤ t.wt w * (p.2 : ℝ) :=
        mul_nonneg (wt_nonneg hw t) (Nat.cast_nonneg _)
      linarith


/-! ### The Huffman code of a finite weighted alphabet -/

/-- The multiset of all leaf labels of a multiset of trees. -/
