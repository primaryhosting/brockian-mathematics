/-
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Belyi Theorem

Category: Frontier Math
Target: `Math2.belyi_theorem`
Provenance: Aristotle theorem prover (Harmonic)

## Contents

This file formalizes Belyi's theorem for the projective line with marked points, i.e. for the
curves `ℙ¹ \ S` where `S` is a finite set of points: such a marked curve is defined over `ℚ̄`
(all points of `S` are algebraic numbers) if and only if there is a Belyi map, i.e. a nonconstant
map `ℙ¹ → ℙ¹` defined over `ℚ` which is ramified only above `{0, 1, ∞}` and which sends `S`
into `{0, 1, ∞}`.

Belyi maps are realized here by polynomials `f ∈ ℚ[X]`; such an `f`, viewed as a self-map of
`ℙ¹`, sends `∞` to `∞`, so ramification above `∞` is automatic and the condition on the
ramification is that all *finite* critical values lie in `{0, 1}`.  This is `Math2.IsBelyi`.

The main result is `Math2.belyi_theorem`.  The non-trivial direction is Belyi's construction,
which is carried out in two steps:

* `Math2.rationalize`: composing with a suitable polynomial over `ℚ` one can force all critical
  values to be rational.  This is the induction on the degrees over `ℚ` of the critical values,
  using that composing with the minimal polynomial of a critical value of maximal degree `D`
  strictly decreases the number of critical values of degree `D`.
* `Math2.rat_reduction`: any finite set of *rational* points can be pushed into `{0, 1}` by a
  Belyi polynomial.  This is Belyi's classical argument with the polynomials
  `x ↦ c · x ^ a (1 - x) ^ n` (`Math2.belyiP`), which have all their critical values in `{0, 1}`
  and collapse `{0, 1, a / (a + n)}` into `{0, 1}`, combined with affine normalizations.
-/

open Polynomial

set_option maxHeartbeats 1000000

namespace Math2

noncomputable section

/-- The degree over `ℚ` of a complex number (`0` if transcendental). -/

private lemma rat_reduction_aux (k : ℕ) : ∀ T : Finset ℚ, T.card ≤ k →
    ∃ h : ℚ[X], IsBelyi h ∧ ∀ t ∈ T, aeval t h = 0 ∨ aeval t h = 1 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro T hTk
  by_cases hcard : T.card ≤ 1
  · rcases T.eq_empty_or_nonempty with rfl | ⟨u, hu⟩
    · refine ⟨X, ⟨by simp, ?_⟩, by simp⟩
      intro z hz
      simp at hz
    · refine ⟨X - C u, ⟨by simp, ?_⟩, ?_⟩
      · intro z hz
        simp at hz
      · intro t ht
        left
        have htu : t = u := Finset.card_le_one.1 hcard t ht u hu
        simp [htu]
  · push_neg at hcard
    have hne : T.Nonempty := Finset.card_pos.1 (by omega)
    set u := T.min' hne with hu_def
    set v := T.max' hne with hv_def
    have huv : u < v := Finset.min'_lt_max'_of_card T hcard
    have hvu : (v - u) ≠ 0 := sub_ne_zero.2 (ne_of_gt huv)
    set A := affP u v with hA_def
    set phi : ℚ → ℚ := fun t => (v - u)⁻¹ * (t - u) with hphi_def
    have hAphi : ∀ t : ℚ, aeval t A = phi t := fun t => aeval_affP_rat u v t
    have hphi_inj : Function.Injective phi := by
      intro x y hxy
      simp only [hphi_def] at hxy
      field_simp at hxy
      linarith
    set U := T.image phi with hU_def
    have hcardU : U.card = T.card := Finset.card_image_of_injective _ hphi_inj
    have h0U : (0 : ℚ) ∈ U := by
      refine Finset.mem_image.2 ⟨u, T.min'_mem hne, ?_⟩
      simp [hphi_def]
    have h1U : (1 : ℚ) ∈ U := by
      refine Finset.mem_image.2 ⟨v, T.max'_mem hne, ?_⟩
      simp [hphi_def]
      field_simp
    have hU01 : ∀ x ∈ U, 0 ≤ x ∧ x ≤ 1 := by
      intro x hx
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hx
      have hle1 : u ≤ t := T.min'_le t ht
      have hle2 : t ≤ v := T.le_max' t ht
      have hpos : (0 : ℚ) < (v - u)⁻¹ := inv_pos.2 (by linarith)
      constructor
      · have htu : (0 : ℚ) ≤ t - u := by linarith
        simp only [hphi_def]
        exact mul_nonneg hpos.le htu
      · simp only [hphi_def]
        rw [inv_mul_le_iff₀ (by linarith : (0:ℚ) < v - u)]
        linarith
    have hAbelyi : IsBelyi A := by
      refine ⟨by rw [affP_natDegree (ne_of_lt huv)]; norm_num, ?_⟩
      intro z hz
      exfalso
      rw [hA_def, derivative_affP] at hz
      simp only [aeval_C, map_eq_zero] at hz
      exact (inv_ne_zero hvu) hz
    by_cases hbig : 3 ≤ T.card
    · -- the main reduction step
      have hlam : ∃ lam ∈ U, lam ≠ 0 ∧ lam ≠ 1 := by
        by_contra hcon
        push_neg at hcon
        have hsub : U ⊆ ({0, 1} : Finset ℚ) := by
          intro x hx
          rcases eq_or_ne x 0 with rfl | hx0
          · simp
          · simp [hcon x hx hx0]
        have := Finset.card_le_card hsub
        have h2 : ({0, 1} : Finset ℚ).card = 2 := by decide
        omega
      obtain ⟨lam, hlamU, hlam0, hlam1⟩ := hlam
      obtain ⟨hlamge, hlamle⟩ := hU01 lam hlamU
      have hlampos : 0 < lam := lt_of_le_of_ne hlamge (Ne.symm hlam0)
      have hlamlt : lam < 1 := lt_of_le_of_ne hlamle hlam1
      set a := lam.num.toNat with ha_def
      set n := lam.den - a with hn_def
      have hnumpos : 0 < lam.num := Rat.num_pos.2 hlampos
      have ha : 0 < a := by omega
      have hnum : (lam.num : ℚ) = (a : ℚ) := by
        rw [ha_def]
        exact_mod_cast (Int.toNat_of_nonneg hnumpos.le).symm
      have haden : a < lam.den := by
        have h1 : (lam.num : ℚ) / (lam.den : ℚ) < 1 := by rw [Rat.num_div_den]; exact hlamlt
        have hd : (0 : ℚ) < (lam.den : ℚ) := by exact_mod_cast lam.pos
        rw [div_lt_one hd] at h1
        have h2 : lam.num < (lam.den : ℤ) := by exact_mod_cast h1
        omega
      have hn : 0 < n := by omega
      have han : a + n = lam.den := by omega
      have hlamval : lam = (a : ℚ) / ((a : ℚ) + (n : ℚ)) := by
        have hd : ((a : ℚ) + (n : ℚ)) = (lam.den : ℚ) := by
          rw [← Nat.cast_add, han]
        rw [hd, ← hnum, Rat.num_div_den]
      set P := belyiP a n with hP_def
      set g : ℚ → ℚ := fun x => aeval x P with hg_def
      have hg0 : g 0 = 0 := aeval_belyiP_zero a n ha
      have hg1 : g 1 = 0 := aeval_belyiP_one a n hn
      have hglam : g lam = 1 := by
        rw [hg_def]
        simp only
        rw [hlamval]
        exact aeval_belyiP_lambda a n ha hn
      set T' := U.image g ∪ ({0, 1} : Finset ℚ) with hT'_def
      have hsub3 : ({0, 1, lam} : Finset ℚ) ⊆ U := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact h0U
        · exact h1U
        · exact hlamU
      have hc3 : ({0, 1, lam} : Finset ℚ).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [Ne.symm hlam0]),
          Finset.card_insert_of_notMem (by simp [Ne.symm hlam1])]
        simp
      have hsubT' : T' ⊆ (U \ ({0, 1, lam} : Finset ℚ)).image g ∪ ({0, 1} : Finset ℚ) := by
        intro y hy
        rcases Finset.mem_union.1 hy with hy | hy
        · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
          by_cases hx3 : x ∈ ({0, 1, lam} : Finset ℚ)
          · refine Finset.mem_union_right _ ?_
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx3 ⊢
            rcases hx3 with rfl | rfl | rfl
            · exact Or.inl hg0
            · exact Or.inl hg1
            · exact Or.inr hglam
          · exact Finset.mem_union_left _
              (Finset.mem_image.2 ⟨x, Finset.mem_sdiff.2 ⟨hx, hx3⟩, rfl⟩)
        · exact Finset.mem_union_right _ hy
      have hcardT' : T'.card < k := by
        have hb1 := Finset.card_le_card hsubT'
        have hb2 := Finset.card_union_le ((U \ ({0, 1, lam} : Finset ℚ)).image g)
          ({0, 1} : Finset ℚ)
        have hb3 := Finset.card_image_le (s := U \ ({0, 1, lam} : Finset ℚ)) (f := g)
        have hb4 : (U \ ({0, 1, lam} : Finset ℚ)).card = U.card - 3 := by
          rw [Finset.card_sdiff_of_subset hsub3, hc3]
        have hb5 : ({0, 1} : Finset ℚ).card = 2 := by decide
        omega
      obtain ⟨h', hb', hT'⟩ := ih T'.card hcardT' T' le_rfl
      have h0T' : (0 : ℚ) ∈ T' := Finset.mem_union_right _ (by simp)
      have h1T' : (1 : ℚ) ∈ T' := Finset.mem_union_right _ (by simp)
      refine ⟨h'.comp (P.comp A), ⟨?_, ?_⟩, ?_⟩
      · rw [Polynomial.natDegree_comp, Polynomial.natDegree_comp]
        have hd1 := hb'.1
        have hd2 := belyiP_natDegree_pos a n ha hn
        have hd3 : A.natDegree = 1 := affP_natDegree (ne_of_lt huv)
        rw [hd3]
        exact Nat.mul_pos hd1 (Nat.mul_pos hd2 (by norm_num))
      · intro z hz
        rw [aeval_derivative_comp] at hz
        rcases mul_eq_zero.1 hz with hz1 | hz2
        · rw [aeval_derivative_comp] at hz1
          rcases mul_eq_zero.1 hz1 with hz3 | hz4
          · exfalso
            rw [hA_def, derivative_affP] at hz3
            simp only [aeval_C, map_eq_zero] at hz3
            exact (inv_ne_zero hvu) hz3
          · have hcrit := belyiP_crit a n ha hn (aeval z A) hz4
            rw [Polynomial.aeval_comp, Polynomial.aeval_comp]
            rcases hcrit with hh | hh
            · rw [hh]
              exact aeval_transfer h' 0 0 (by simp) (hT' 0 h0T')
            · rw [hh]
              exact aeval_transfer h' 1 1 (by simp) (hT' 1 h1T')
        · rw [Polynomial.aeval_comp]
          exact hb'.2 (aeval z (P.comp A)) hz2
      · intro t ht
        rw [Polynomial.aeval_comp, Polynomial.aeval_comp, hAphi]
        refine hT' _ (Finset.mem_union_left _ (Finset.mem_image.2 ⟨phi t, ?_, rfl⟩))
        exact Finset.mem_image.2 ⟨t, ht, rfl⟩
    · -- exactly two points: the affine map already works
      have hcard2 : T.card = 2 := by omega
      have hUeq : ({0, 1} : Finset ℚ) = U := by
        refine Finset.eq_of_subset_of_card_le ?_ ?_
        · intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact h0U
          · exact h1U
        · have h2 : ({0, 1} : Finset ℚ).card = 2 := by decide
          omega
      refine ⟨A, hAbelyi, ?_⟩
      intro t ht
      have hmem : phi t ∈ U := Finset.mem_image.2 ⟨t, ht, rfl⟩
      rw [← hUeq] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rw [hAphi]
      exact hmem

/-- **Belyi's reduction over `ℚ`**: for every finite set `T` of rational numbers there is a
Belyi polynomial mapping `T` into `{0, 1}`. -/
