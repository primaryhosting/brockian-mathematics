import RequestProject.HuffmanKraft

/-!
# Weighted depth multisets, the Huffman merging process, and the optimality bound
-/

namespace CS

/-- A *weighted depth multiset*: a finite multiset of pairs `(weight, codeword length)`. -/
abbrev WD := Multiset (ℝ × ℕ)

/-- The expected codeword length associated to a weighted depth multiset. -/

theorem normalize_aux : ∀ (n : ℕ) (D : WD), (dps D).sum = n → (∀ p ∈ D, 0 ≤ p.1) → D ≠ 0 →
    kraft D ≤ 1 → ∃ D' : WD, wts D' = wts D ∧ kraft D' = 1 ∧ cost D' ≤ cost D := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro D hsum hw hD hk
    rcases eq_or_lt_of_le hk with heq | hlt
    · exact ⟨D, rfl, heq, le_refl _⟩
    obtain ⟨M, hM, hMmax⟩ := exists_max_mem (dps D) (by simpa [dps] using hD)
    have hmax : ∀ q ∈ D, q.2 ≤ M := fun q hq => hMmax q.2 (Multiset.mem_map_of_mem _ hq)
    obtain ⟨p, hp, hpM⟩ := Multiset.mem_map.1 hM
    rcases Nat.eq_zero_or_pos M with hM0 | hM1
    · exfalso
      have hz : ∀ q ∈ D, q.2 = 0 := fun q hq => Nat.le_zero.1 (hM0 ▸ hmax q hq)
      rw [kraft_of_depths_zero hz] at hlt
      have h1 : 1 ≤ D.card := Multiset.card_pos.2 hD
      have h2 : (1 : ℝ) ≤ (D.card : ℝ) := by exact_mod_cast h1
      linarith
    have hnum : kraft D * 2 ^ M = (kn M D : ℝ) := kraft_eq_kn M D hmax
    have hpow : (0 : ℝ) < 2 ^ M := by positivity
    have hlt' : (kn M D : ℝ) < 2 ^ M := by
      rw [← hnum]
      calc kraft D * 2 ^ M < 1 * 2 ^ M := mul_lt_mul_of_pos_right hlt hpow
        _ = 2 ^ M := one_mul _
    have hknle : kn M D + 1 ≤ 2 ^ M := by
      have : kn M D < 2 ^ M := by exact_mod_cast hlt'
      omega
    have hbound : kraft D + (1 / 2 : ℝ) ^ M ≤ 1 := by
      have h1 : (kn M D : ℝ) + 1 ≤ 2 ^ M := by exact_mod_cast hknle
      have h2 : kraft D * 2 ^ M + 1 ≤ 2 ^ M := by rw [hnum]; exact h1
      have h3 : (1 / 2 : ℝ) ^ M = 1 / 2 ^ M := by rw [div_pow, one_pow]
      rw [h3, ← sub_nonneg]
      have h4 : 1 - (kraft D + 1 / 2 ^ M) = (2 ^ M - kraft D * 2 ^ M - 1) / 2 ^ M := by
        field_simp
        ring
      rw [h4]
      apply div_nonneg _ (le_of_lt hpow)
      linarith
    set E : WD := D.erase p with hE
    have hDeq : D = p ::ₘ E := (Multiset.cons_erase hp).symm
    set D' : WD := (p.1, M - 1) ::ₘ E with hD'
    have hcastM : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
      have h1 : (1 : ℕ) ≤ M := hM1
      push_cast [Nat.cast_sub h1]
      ring
    have hkraftE : kraft D = (1 / 2 : ℝ) ^ M + kraft E := by
      conv_lhs => rw [hDeq]
      rw [kraft_cons, hpM]
    have hpowsub : (1 / 2 : ℝ) ^ (M - 1) = 2 * (1 / 2 : ℝ) ^ M := by
      obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
      simp [pow_succ]
      ring
    have hkD' : kraft D' = kraft D + (1 / 2 : ℝ) ^ M := by
      rw [hD', kraft_cons, hpowsub, hkraftE]
      ring
    have hcostD' : cost D' ≤ cost D := by
      have hcD : cost D = p.1 * (M : ℝ) + cost E := by
        conv_lhs => rw [hDeq]
        rw [cost_cons, hpM]
      rw [hD', cost_cons, hcD, hcastM]
      have hp1 : 0 ≤ p.1 := hw p hp
      nlinarith
    have hwD' : wts D' = wts D := by
      conv_rhs => rw [hDeq]
      rw [hD', wts_cons, wts_cons]
    have hsum' : (dps D').sum < n := by
      have h1 : (dps D).sum = M + (dps E).sum := by
        conv_lhs => rw [hDeq]
        rw [dps_cons, Multiset.sum_cons, hpM]
      have h2 : (dps D').sum = (M - 1) + (dps E).sum := by
        rw [hD', dps_cons, Multiset.sum_cons]
      omega
    obtain ⟨D'', hw'', hk'', hc''⟩ := ih _ hsum' D' rfl
      (by
        intro q hq
        rcases Multiset.mem_cons.1 hq with rfl | hq
        · exact hw p hp
        · exact hw q (by rw [hDeq]; exact Multiset.mem_cons_of_mem hq))
      (by simp [hD'])
      (by rw [hkD']; exact hbound)
    exact ⟨D'', by rw [hw'', hwD'], hk'', le_trans hc'' hcostD'⟩

