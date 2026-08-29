/-
# Sunflower Bound
Category: Frontier Math
Target: Math2.sunflower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Sunflower Bound
Category: Frontier Math
Target: Math2.sunflower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math2

variable {α : Type*} [DecidableEq α]

/-- A family `S` of sets is a *sunflower with core `c`* if any two distinct members of `S`
intersect exactly in `c`. -/

theorem sunflower_of_spreadDisjoint {rho : ℕ → ℕ → ℝ}
    (hmono : ∀ p k k' : ℕ, 2 ≤ p → 1 ≤ k' → k' ≤ k → rho p k' ≤ rho p k)
    (hge : ∀ p k : ℕ, 2 ≤ p → 1 ≤ k → (p : ℝ) ≤ rho p k)
    (h : SpreadDisjoint (α := α) rho) :
    ∀ (k p : ℕ), 2 ≤ p → 1 ≤ k → ∀ F : Finset (Finset α), (∀ A ∈ F, A.card = k) →
      (rho p k) ^ k ≤ (F.card : ℝ) → HasSunflower F p := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro p hp hk F hF hcard
    have hp0 : (0 : ℝ) < p := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp
      linarith
    have hrho_pos : ∀ m : ℕ, 1 ≤ m → (0 : ℝ) < rho p m := fun m hm =>
      lt_of_lt_of_le hp0 (hge p m hp hm)
    rcases eq_or_lt_of_le hk with hk1 | hk2
    · -- `k = 1`: any `p` distinct singletons are pairwise disjoint
      subst hk1
      have hpF : p ≤ F.card := by
        have : (p : ℝ) ≤ (F.card : ℝ) := by
          calc (p : ℝ) ≤ rho p 1 := hge p 1 hp le_rfl
            _ = (rho p 1) ^ 1 := (pow_one _).symm
            _ ≤ (F.card : ℝ) := hcard
        exact_mod_cast this
      obtain ⟨D, hDF, hDcard⟩ := Finset.exists_subset_card_eq hpF
      refine hasSunflower_of_disjoint hDF hDcard ?_
      intro A hA B hB hAB
      obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp (hF A (hDF hA))
      obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp (hF B (hDF hB))
      simp only [Finset.disjoint_singleton]
      simpa using hAB
    -- `k ≥ 2`
    by_cases hs : IsSpread F k (rho p k)
    · obtain ⟨D, hDF, hDcard, hdisj⟩ := h p k hp hk F hF hs hcard
      exact hasSunflower_of_disjoint hDF hDcard hdisj
    · -- some nonempty `T` has a large link; induct on the link
      simp only [IsSpread, not_forall, not_le] at hs
      obtain ⟨T, hTne, hTbig⟩ := hs
      have hTk : T.card < k := by
        by_contra hcon
        push_neg at hcon
        have hsub : F.filter (fun A => T ⊆ A) ⊆ {T} := by
          intro A hA
          rw [Finset.mem_filter] at hA
          have : A = T := (Finset.eq_of_subset_of_card_le hA.2 (by
            rw [hF A hA.1]; exact hcon)).symm
          simp [this]
        have h1 : ((F.filter (fun A => T ⊆ A)).card : ℝ) ≤ 1 := by
          have := Finset.card_le_card hsub
          simp only [Finset.card_singleton] at this
          exact_mod_cast this
        have h2 : k - T.card = 0 := by omega
        rw [h2, pow_zero] at hTbig
        linarith
      have hT1 : 1 ≤ T.card := Finset.card_pos.mpr hTne
      obtain ⟨k', hk'⟩ : ∃ k', k' = k - T.card := ⟨k - T.card, rfl⟩
      have hk'1 : 1 ≤ k' := by omega
      have hk'k : k' < k := by omega
      set L : Finset (Finset α) := (F.filter (fun A => T ⊆ A)).image (fun A => A \ T) with hL
      have hLcard : L.card = (F.filter (fun A => T ⊆ A)).card := by
        rw [hL]
        refine Finset.card_image_of_injOn ?_
        intro A hA B hB hAB
        simp only [Finset.mem_coe, Finset.mem_filter] at hA hB
        simp only at hAB
        calc A = A \ T ∪ T := (Finset.sdiff_union_of_subset hA.2).symm
          _ = B \ T ∪ T := by rw [hAB]
          _ = B := Finset.sdiff_union_of_subset hB.2
      have hLsize : ∀ B ∈ L, B.card = k' := by
        intro B hB
        rw [hL, Finset.mem_image] at hB
        obtain ⟨A, hA, rfl⟩ := hB
        rw [Finset.mem_filter] at hA
        rw [Finset.card_sdiff_of_subset hA.2, hF A hA.1, hk']
      have hLbound : (rho p k') ^ k' ≤ (L.card : ℝ) := by
        have h1 : (rho p k') ^ k' ≤ (rho p k) ^ k' :=
          pow_le_pow_left₀ (le_of_lt (hrho_pos k' hk'1)) (hmono p k k' hp hk'1 (le_of_lt hk'k)) k'
        rw [← hk'] at hTbig
        rw [hLcard]
        linarith
      obtain ⟨S', hS'L, hS'card, c, hc⟩ := ih k' hk'k p hp hk'1 L hLsize hLbound
      have hmemF : ∀ B ∈ S', B ∪ T ∈ F := by
        intro B hB
        have := hS'L hB
        rw [hL, Finset.mem_image] at this
        obtain ⟨A, hA, rfl⟩ := this
        rw [Finset.mem_filter] at hA
        rw [Finset.sdiff_union_of_subset hA.2]
        exact hA.1
      have hdisjT : ∀ B ∈ S', Disjoint B T := by
        intro B hB
        have := hS'L hB
        rw [hL, Finset.mem_image] at this
        obtain ⟨A, -, rfl⟩ := this
        exact Finset.sdiff_disjoint
      refine ⟨S'.image (fun B => B ∪ T), ?_, ?_, c ∪ T, ?_⟩
      · intro A hA
        rw [Finset.mem_image] at hA
        obtain ⟨B, hB, rfl⟩ := hA
        exact hmemF B hB
      · rw [Finset.card_image_of_injOn, hS'card]
        intro A hA B hB hAB
        simp only [Finset.mem_coe] at hA hB
        simp only at hAB
        calc A = (A ∪ T) \ T := (Finset.union_sdiff_cancel_right (hdisjT A hA)).symm
          _ = (B ∪ T) \ T := by rw [hAB]
          _ = B := Finset.union_sdiff_cancel_right (hdisjT B hB)
      · intro A hA B hB hAB
        rw [Finset.mem_image] at hA hB
        obtain ⟨A', hA', rfl⟩ := hA
        obtain ⟨B', hB', rfl⟩ := hB
        have hne : A' ≠ B' := by rintro rfl; exact hAB rfl
        have hdist : (A' ∪ T) ∩ (B' ∪ T) = (A' ∩ B') ∪ T := by
          ext z
          simp only [Finset.mem_inter, Finset.mem_union]
          tauto
        rw [hdist, hc A' hA' B' hB' hne]

/-- The elementary greedy bound: the threshold `rho p k = p * k` has the spread-to-disjoint
property. -/
