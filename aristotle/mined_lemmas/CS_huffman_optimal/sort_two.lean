import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


theorem sort_two (C W : β → ℝ) (b1 b2 : β) (h12 : W b1 ≤ W b2) :
    ∀ (N : Multiset (β × ℕ)), (∀ p ∈ N, W b2 ≤ W p.1) → ∀ (x y : ℕ),
      ∃ (x' y' : ℕ) (N' : Multiset (β × ℕ)),
        N'.map Prod.fst = N.map Prod.fst ∧
        kraftL (klen ((b1, x') ::ₘ (b2, y') ::ₘ N'))
          = kraftL (klen ((b1, x) ::ₘ (b2, y) ::ₘ N)) ∧
        y' ≤ x' ∧ (∀ p ∈ N', p.2 ≤ y') ∧
        gcost C W ((b1, x') ::ₘ (b2, y') ::ₘ N')
          ≤ gcost C W ((b1, x) ::ₘ (b2, y) ::ₘ N) := by
  intro N
  induction N using Multiset.induction_on with
  | empty =>
      intro _ x y
      rcases le_total x y with hxy | hxy
      · refine ⟨y, x, 0, rfl, by simp [klen, kraftL]; ring, hxy, by simp, ?_⟩
        have hx : (x:ℝ) ≤ y := by exact_mod_cast hxy
        simp only [gcost_cons, gcost_zero]
        nlinarith [mul_nonneg (sub_nonneg.2 h12) (sub_nonneg.2 hx)]
      · exact ⟨x, y, 0, rfl, by simp, hxy, by simp, le_refl _⟩
  | cons q N ih =>
      intro hmem x y
      have hqW : W b2 ≤ W q.1 := hmem q (Multiset.mem_cons_self q N)
      have hNW : ∀ p ∈ N, W b2 ≤ W p.1 := fun p hp => hmem p (Multiset.mem_cons_of_mem hp)
      obtain ⟨x', y', N', hfst, hkr, hyx, hbd, hcost⟩ := ih hNW x y
      obtain ⟨u, c⟩ := q
      simp only at hqW ⊢
      by_cases hc : c ≤ y'
      · refine ⟨x', y', (u, c) ::ₘ N', by simp [hfst], ?_, hyx, ?_, ?_⟩
        · simp only [klen_cons, kraftL_cons] at hkr ⊢
          linarith
        · intro p hp
          rcases Multiset.mem_cons.1 hp with rfl | hp
          · exact hc
          · exact hbd p hp
        · simp only [gcost_cons] at hcost ⊢
          linarith
      · push_neg at hc
        by_cases hcx : c ≤ x'
        · refine ⟨x', c, (u, y') ::ₘ N', by simp [hfst], ?_, hcx, ?_, ?_⟩
          · simp only [klen_cons, kraftL_cons] at hkr ⊢
            linarith
          · intro p hp
            rcases Multiset.mem_cons.1 hp with rfl | hp
            · exact le_of_lt hc
            · exact le_trans (hbd p hp) (le_of_lt hc)
          · have hcy : (y':ℝ) ≤ (c:ℝ) := by exact_mod_cast le_of_lt hc
            simp only [gcost_cons] at hcost ⊢
            nlinarith [mul_nonneg (sub_nonneg.2 hqW) (sub_nonneg.2 hcy)]
        · push_neg at hcx
          refine ⟨c, x', (u, y') ::ₘ N', by simp [hfst], ?_, le_of_lt hcx, ?_, ?_⟩
          · simp only [klen_cons, kraftL_cons] at hkr ⊢
            linarith
          · intro p hp
            rcases Multiset.mem_cons.1 hp with rfl | hp
            · exact hyx
            · exact le_trans (hbd p hp) hyx
          · have hcx' : (x':ℝ) ≤ (c:ℝ) := by exact_mod_cast le_of_lt hcx
            have hyx' : (y':ℝ) ≤ (x':ℝ) := by exact_mod_cast hyx
            have h1u : W b1 ≤ W u := le_trans h12 hqW
            simp only [gcost_cons] at hcost ⊢
            nlinarith [mul_nonneg (sub_nonneg.2 h1u) (sub_nonneg.2 hcx'),
              mul_nonneg (sub_nonneg.2 hqW) (sub_nonneg.2 hyx')]

/-- If `b1` carries a length larger than all the others, it may be lowered to the length of
`b2` without breaking Kraft's inequality. -/
