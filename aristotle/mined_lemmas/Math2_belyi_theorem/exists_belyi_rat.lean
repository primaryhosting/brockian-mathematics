import Mathlib
/-!
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Classical

set_option maxHeartbeats 1000000

namespace Math2

open Polynomial IntermediateField

noncomputable section

/-! ## Basic notions -/

/-- The set of critical values in `ℂ` of a polynomial with rational coefficients.
Viewing `f ∈ ℚ[X]` as a morphism `ℙ¹ → ℙ¹`, these are the finite branch points of `f`. -/

lemma exists_belyi_rat (n : ℕ) : ∀ T : Finset ℚ, T.card ≤ n →
    ∃ f : ℚ[X], 0 < f.natDegree ∧ (∀ t ∈ T, f.eval t = 0 ∨ f.eval t = 1) ∧
      critVal f ⊆ ({0, 1} : Set ℂ) := by
  induction n with
  | zero => intro T _; exact belyi_rat_base T (by omega)
  | succ n ih =>
    intro T hT
    by_cases h3 : T.card ≤ 2
    · exact belyi_rat_base T h3
    push_neg at h3
    have hne : T.Nonempty := Finset.card_pos.mp (by omega)
    set a := T.min' hne with hadef
    set b := T.max' hne with hbdef
    have haT : a ∈ T := T.min'_mem hne
    have hbT : b ∈ T := T.max'_mem hne
    have hab : a < b := T.min'_lt_max'_of_card (by omega)
    have hne' : a ≠ b := ne_of_lt hab
    have hsub : T ⊆ (T \ {a, b}) ∪ {a, b} := by
      intro t ht
      by_cases h : t ∈ ({a, b} : Finset ℚ)
      · exact Finset.mem_union_right _ h
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ht, h⟩)
    have hcard2 : ({a, b} : Finset ℚ).card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
    have hthird : (T \ ({a, b} : Finset ℚ)).Nonempty := by
      rw [← Finset.card_pos]
      by_contra hcon
      push_neg at hcon
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_union_le (T \ ({a, b} : Finset ℚ)) ({a, b} : Finset ℚ)
      omega
    obtain ⟨c, hc⟩ := hthird
    have hcT : c ∈ T := (Finset.mem_sdiff.mp hc).1
    have hcab : c ≠ a ∧ c ≠ b := by
      have h := (Finset.mem_sdiff.mp hc).2
      simpa using h
    have hac : a < c := lt_of_le_of_ne (T.min'_le c hcT) (Ne.symm hcab.1)
    have hcb : c < b := lt_of_le_of_ne (T.le_max' c hcT) hcab.2
    set μ := (c - a) / (b - a) with hmu
    have hba : (0 : ℚ) < b - a := by linarith
    have hmu0 : 0 < μ := div_pos (by linarith) hba
    have hmu1 : μ < 1 := by rw [hmu, div_lt_one hba]; linarith
    obtain ⟨p, q, hpq⟩ := exists_belyiPt μ hmu0 hmu1
    set A := affQ a b with hA
    set B := belyiPoly p q with hB
    set F := B.comp A with hF
    have hFa : F.eval a = 0 := by
      rw [hF, eval_comp, affQ_eval]
      simp [hB, belyiPoly_eval_zero]
    have hFb : F.eval b = 0 := by
      rw [hF, eval_comp, affQ_eval, div_self (by linarith : b - a ≠ 0)]
      simp [hB, belyiPoly_eval_one]
    have hFc : F.eval c = 1 := by
      rw [hF, eval_comp, affQ_eval, ← hmu, ← hpq]
      exact belyiPoly_eval_pt p q
    set T' := T.image (fun t => F.eval t) with hT'
    have h0T' : (0 : ℚ) ∈ T' := by rw [hT']; exact Finset.mem_image.mpr ⟨a, haT, hFa⟩
    have h1T' : (1 : ℚ) ∈ T' := by rw [hT']; exact Finset.mem_image.mpr ⟨c, hcT, hFc⟩
    have himg : T' = (T.erase b).image (fun t => F.eval t) := by
      apply Finset.Subset.antisymm
      · intro v hv
        rw [hT'] at hv
        obtain ⟨t, htT, htv⟩ := Finset.mem_image.mp hv
        by_cases hb' : t = b
        · exact Finset.mem_image.mpr ⟨a, Finset.mem_erase.mpr ⟨hne', haT⟩,
            by rw [hFa, ← htv, hb', hFb]⟩
        · exact Finset.mem_image.mpr ⟨t, Finset.mem_erase.mpr ⟨hb', htT⟩, htv⟩
      · intro v hv
        obtain ⟨t, htT, htv⟩ := Finset.mem_image.mp hv
        rw [hT']
        exact Finset.mem_image.mpr ⟨t, (Finset.mem_erase.mp htT).2, htv⟩
    have hcardT' : T'.card ≤ n := by
      rw [himg]
      have h1 := Finset.card_image_le (s := T.erase b) (f := fun t => F.eval t)
      have h2 : (T.erase b).card = T.card - 1 := Finset.card_erase_of_mem hbT
      omega
    obtain ⟨g, hgdeg, hgeval, hgcrit⟩ := ih T' hcardT'
    have hFdeg : 0 < F.natDegree := by
      rw [hF, natDegree_comp, hA, affQ_natDegree a b hne']
      simpa [hB] using belyiPoly_natDegree_pos p q
    have hcritF : critVal F ⊆ ({0, 1} : Set ℂ) := by
      intro v hv
      rcases critVal_comp B A hv with ⟨u, hu, _⟩ | hv'
      · rw [hA, critVal_affQ a b hne'] at hu; exact absurd hu (Set.notMem_empty u)
      · exact critVal_belyiPoly p q hv'
    refine ⟨g.comp F, ?_, ?_, ?_⟩
    · rw [natDegree_comp]; exact Nat.mul_pos hgdeg hFdeg
    · intro t ht
      rw [eval_comp]
      exact hgeval _ (by rw [hT']; exact Finset.mem_image.mpr ⟨t, ht, rfl⟩)
    · intro v hv
      rcases critVal_comp g F hv with ⟨u, hu, huv⟩ | hv'
      · have hu' := hcritF hu
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu'
        have hg0 : aeval (0 : ℂ) g = ((g.eval 0 : ℚ) : ℂ) := by
          simpa using aeval_ratCast (0 : ℚ) g
        have hg1 : aeval (1 : ℂ) g = ((g.eval 1 : ℚ) : ℂ) := by
          simpa using aeval_ratCast (1 : ℚ) g
        rcases hu' with rfl | rfl
        · rw [← huv]
          simp only [hg0]
          rcases hgeval 0 h0T' with h | h <;> rw [h] <;> simp
        · rw [← huv]
          simp only [hg1]
          rcases hgeval 1 h1T' with h | h <;> rw [h] <;> simp
      · exact hgcrit hv'

/-! ## Step 2 : mapping a finite set of algebraic numbers into `ℚ` -/

/-- The (finite) set of critical values of `f`. -/
