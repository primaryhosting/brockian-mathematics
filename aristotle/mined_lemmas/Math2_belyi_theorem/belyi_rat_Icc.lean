import Mathlib

/-!
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial
open scoped IntermediateField

namespace Math2

/-- A *Belyi map* (in the genus-zero, polynomial model): a nonconstant polynomial with
rational coefficients, viewed as a morphism `ℙ¹ → ℙ¹` defined over `ℚ`, all of whose
finite critical values lie in `{0, 1}`.  Being a polynomial, such a map is totally
ramified over `∞`, so it is ramified only above `{0, 1, ∞}`. -/

theorem belyi_rat_Icc : ∀ (k : ℕ) (T : Finset ℚ), (∀ t ∈ T, 0 ≤ t ∧ t ≤ 1) →
    (T.filter (fun t => t ≠ 0 ∧ t ≠ 1)).card ≤ k →
    BelyiFor ((fun q : ℚ => (q : ℂ)) '' (T : Set ℚ)) := by
  intro k
  induction k with
  | zero =>
    intro T _ hcard
    refine belyi_zero_one _ ?_
    rintro s ⟨t, ht, rfl⟩
    have hnot : t ∉ T.filter (fun t => t ≠ 0 ∧ t ≠ 1) := by
      rw [Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)]; simp
    simp only [Finset.mem_filter, not_and, not_not] at hnot
    have h01 : t = 0 ∨ t = 1 := by
      by_cases h : t = 0
      · exact Or.inl h
      · exact Or.inr (hnot ht h)
    rcases h01 with rfl | rfl <;> simp
  | succ k ih =>
    intro T hT hcard
    by_cases hempty : ∀ t ∈ T, t = 0 ∨ t = 1
    · refine belyi_zero_one _ ?_
      rintro s ⟨t, ht, rfl⟩
      rcases hempty t ht with rfl | rfl <;> simp
    · push_neg at hempty
      obtain ⟨l, hlT, hl0, hl1⟩ := hempty
      obtain ⟨hl0', hl1'⟩ := hT l hlT
      have hlpos : 0 < l := lt_of_le_of_ne hl0' (Ne.symm hl0)
      have hllt : l < 1 := lt_of_le_of_ne hl1' hl1
      obtain ⟨m, n, hmn⟩ := exists_ratio l hlpos hllt
      have hgl : (belyiPush (m + 1) (n + 1)).eval l = 1 := by
        rw [hmn]; exact belyiPush_eval_ratio m n
      set g := belyiPush (m + 1) (n + 1) with hg
      set T₁ : Finset ℚ := insert 0 (insert 1 (T.image (fun t => g.eval t))) with hT₁
      have hmem01 : ∀ t ∈ T₁, 0 ≤ t ∧ t ≤ 1 := by
        intro t ht
        simp only [hT₁, Finset.mem_insert, Finset.mem_image] at ht
        rcases ht with rfl | rfl | ⟨u, hu, rfl⟩
        · norm_num
        · norm_num
        · exact belyiPush_mem_Icc m n (hT u hu).1 (hT u hu).2
      have hlfilter : l ∈ T.filter (fun t => t ≠ 0 ∧ t ≠ 1) :=
        Finset.mem_filter.mpr ⟨hlT, hl0, hl1⟩
      have hcard₁ : (T₁.filter (fun t => t ≠ 0 ∧ t ≠ 1)).card ≤ k := by
        have hsub : T₁.filter (fun t => t ≠ 0 ∧ t ≠ 1) ⊆
            ((T.filter (fun t => t ≠ 0 ∧ t ≠ 1)).erase l).image (fun t => g.eval t) := by
          intro x hx
          rw [Finset.mem_filter] at hx
          obtain ⟨hxmem, hx0, hx1⟩ := hx
          simp only [hT₁, Finset.mem_insert, Finset.mem_image] at hxmem
          rcases hxmem with rfl | rfl | ⟨t, ht, rfl⟩
          · exact absurd rfl hx0
          · exact absurd rfl hx1
          · refine Finset.mem_image.mpr
              ⟨t, Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr ⟨ht, ?_, ?_⟩⟩, rfl⟩
            · rintro rfl; exact hx1 hgl
            · rintro rfl; exact hx0 (belyiPush_eval_zero m n)
            · rintro rfl; exact hx0 (belyiPush_eval_one m n)
        have h1 := Finset.card_le_card hsub
        have h2 := Finset.card_image_le (s := (T.filter (fun t => t ≠ 0 ∧ t ≠ 1)).erase l)
          (f := fun t => g.eval t)
        have h3 : ((T.filter (fun t => t ≠ 0 ∧ t ≠ 1)).erase l).card
            = (T.filter (fun t => t ≠ 0 ∧ t ≠ 1)).card - 1 :=
          Finset.card_erase_of_mem hlfilter
        have h4 : 1 ≤ (T.filter (fun t => t ≠ 0 ∧ t ≠ 1)).card :=
          Finset.card_pos.mpr ⟨l, hlfilter⟩
        omega
      refine belyi_comp g (belyiPush_natDegree m n) _ _ ?_ ?_ (ih T₁ hmem01 hcard₁)
      · intro z hz
        rcases belyiPush_crit m n z hz with h | h
        · refine ⟨0, by simp [hT₁], ?_⟩
          have hgz : aeval z g = 0 := h
          simp [hgz]
        · refine ⟨1, by simp [hT₁], ?_⟩
          have hgz : aeval z g = 1 := h
          simp [hgz]
      · rintro s ⟨t, ht, rfl⟩
        refine ⟨g.eval t, ?_, ?_⟩
        · simp only [hT₁, Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, Finset.mem_image]
          exact Or.inr (Or.inr ⟨t, ht, rfl⟩)
        · rw [aeval_rat]

/-- Belyi's theorem for an arbitrary finite set of rational points. -/
