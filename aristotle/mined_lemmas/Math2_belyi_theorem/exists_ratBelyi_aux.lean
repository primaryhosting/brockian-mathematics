import RequestProject.BelyiPoly

/-!
# Belyi polynomials for finite sets of rational points

A polynomial `f ∈ ℚ[X]` is *Belyi* if it is non-constant and all of its finite critical values
(computed over `ℂ`) lie in `{0, 1}`; viewed as a map `ℙ¹ → ℙ¹` such an `f` is ramified only
above `{0, 1, ∞}`.

The main result of this file is `Math2.exists_belyiPolynomial_of_rat`: for every finite set of
rational numbers there is a Belyi polynomial taking each of them to `0` or `1`.
-/

set_option maxRecDepth 8000

namespace Math2

open Polynomial

/-- `f` is a Belyi polynomial: non-constant, with all finite critical values in `{0, 1}`. -/

lemma exists_ratBelyi_aux : ∀ (k : ℕ) (S : Finset ℚ), (∀ x ∈ S, 0 ≤ x ∧ x ≤ 1) →
    (S.filter (fun x => x ≠ 0 ∧ x ≠ 1)).card ≤ k → ∃ f : ℚ[X], RatBelyi S f := by
  intro k
  induction k with
  | zero =>
    intro S _ hcard
    refine ⟨X, isBelyiPolynomial_X, ?_, by simp, by simp, ?_⟩
    · intro x hx
      have hempty : S.filter (fun x => x ≠ 0 ∧ x ≠ 1) = ∅ := Finset.card_eq_zero.1 (by omega)
      by_contra hcon
      push_neg at hcon
      have : x ∈ S.filter (fun x => x ≠ 0 ∧ x ≠ 1) := by
        simp only [Finset.mem_filter]
        refine ⟨hx, ?_, ?_⟩
        · simpa using hcon.1
        · simpa using hcon.2
      rw [hempty] at this
      simp at this
    · intro x hx0 hx1
      simpa using ⟨hx0, hx1⟩
  | succ k ih =>
    intro S hS hcard
    by_cases hne : (S.filter (fun x => x ≠ 0 ∧ x ≠ 1)).Nonempty
    · obtain ⟨lam, hlam⟩ := hne
      rw [Finset.mem_filter] at hlam
      obtain ⟨hlamS, hlam0, hlam1⟩ := hlam
      have hb := hS lam hlamS
      have h0 : 0 < lam := lt_of_le_of_ne hb.1 (Ne.symm hlam0)
      have h1 : lam < 1 := lt_of_le_of_ne hb.2 hlam1
      obtain ⟨m, n, hm, hn, hmn⟩ := exists_num_den h0 h1
      set B := belyiPoly m n with hB
      set e : ℚ → ℚ := fun x => B.eval x with he
      set S' : Finset ℚ := S.image e with hS'
      -- the new set is again contained in the unit interval
      have hS'mem : ∀ y ∈ S', 0 ≤ y ∧ y ≤ 1 := by
        intro y hy
        rw [hS', Finset.mem_image] at hy
        obtain ⟨x, hx, rfl⟩ := hy
        exact belyiPoly_eval_mem_Icc hm hn (hS x hx).1 (hS x hx).2
      -- the number of points outside `{0,1}` strictly decreases
      have hsub : S'.filter (fun y => y ≠ 0 ∧ y ≠ 1) ⊆
          ((S.filter (fun x => x ≠ 0 ∧ x ≠ 1)).erase lam).image e := by
        intro y hy
        rw [Finset.mem_filter, hS', Finset.mem_image] at hy
        obtain ⟨⟨x, hxS, rfl⟩, hy0, hy1⟩ := hy
        have hx0 : x ≠ 0 := by
          rintro rfl
          exact hy0 (by simpa [he, hB] using belyiPoly_eval_zero (m := m) (n := n) hm)
        have hx1 : x ≠ 1 := by
          rintro rfl
          exact hy0 (by simpa [he, hB] using belyiPoly_eval_one (m := m) (n := n) hn)
        have hxlam : x ≠ lam := by
          rintro rfl
          refine hy1 ?_
          have : (belyiPoly m n).eval ((m : ℚ) / ((m : ℚ) + (n : ℚ))) = 1 :=
            belyiPoly_eval_lambda hm hn
          rw [hmn] at this
          simpa [he, hB] using this
        exact Finset.mem_image.2 ⟨x, Finset.mem_erase.2 ⟨hxlam,
          Finset.mem_filter.2 ⟨hxS, hx0, hx1⟩⟩, rfl⟩
      have hcard' : (S'.filter (fun y => y ≠ 0 ∧ y ≠ 1)).card ≤ k := by
        have h2 := Finset.card_le_card hsub
        have h3 := Finset.card_image_le (s := (S.filter (fun x => x ≠ 0 ∧ x ≠ 1)).erase lam) (f := e)
        have h4 : ((S.filter (fun x => x ≠ 0 ∧ x ≠ 1)).erase lam).card
            = (S.filter (fun x => x ≠ 0 ∧ x ≠ 1)).card - 1 :=
          Finset.card_erase_of_mem (Finset.mem_filter.2 ⟨hlamS, hlam0, hlam1⟩)
        have h5 : 1 ≤ (S.filter (fun x => x ≠ 0 ∧ x ≠ 1)).card :=
          Finset.card_pos.2 ⟨lam, Finset.mem_filter.2 ⟨hlamS, hlam0, hlam1⟩⟩
        omega
      obtain ⟨g, hg⟩ := ih S' hS'mem hcard'
      obtain ⟨hgB, hgS, hg0, hg1, hgIcc⟩ := hg
      refine ⟨g.comp B, ?_, ?_, ?_, ?_, ?_⟩
      · refine IsBelyiPolynomial.comp (by rw [hB, belyiPoly_natDegree hm hn]; omega) hgB ?_
        · intro z hz
          have hcv := belyiPoly_critical_value hm hn z hz
          rcases hcv with hcv | hcv <;> rw [hcv]
          · have : aeval ((0 : ℚ) : ℂ) g = 0 ∨ aeval ((0 : ℚ) : ℂ) g = 1 := aeval_rat_mem hg0
            simpa using this
          · have : aeval ((1 : ℚ) : ℂ) g = 0 ∨ aeval ((1 : ℚ) : ℂ) g = 1 := aeval_rat_mem hg1
            simpa using this
      · intro x hx
        rw [eval_comp]
        exact hgS _ (Finset.mem_image.2 ⟨x, hx, rfl⟩)
      · rw [eval_comp, hB, belyiPoly_eval_zero (m := m) (n := n) hm]
        exact hg0
      · rw [eval_comp, hB, belyiPoly_eval_one (m := m) (n := n) hn]
        exact hg0
      · intro x hx0 hx1
        rw [eval_comp]
        have := belyiPoly_eval_mem_Icc hm hn hx0 hx1
        exact hgIcc _ this.1 this.2
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      refine ⟨X, isBelyiPolynomial_X, ?_, by simp, by simp, ?_⟩
      · intro x hx
        by_contra hcon
        push_neg at hcon
        have : x ∈ S.filter (fun x => x ≠ 0 ∧ x ≠ 1) := by
          simp only [Finset.mem_filter]
          exact ⟨hx, by simpa using hcon.1, by simpa using hcon.2⟩
        rw [hne] at this
        simp at this
      · intro x hx0 hx1
        simpa using ⟨hx0, hx1⟩

/-- Belyi's construction for a finite set of rationals contained in `[0,1]`. -/
