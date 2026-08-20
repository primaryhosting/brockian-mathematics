import RequestProject.Mertens

/-!
# The main term: `∏_{3 ≤ p ≤ z} (1 - 2/p) ≤ 16 / (log z)^2`

This is proved by the elementary Euler-type argument: expanding `∏ (1 + 1/(p-1))` over
subsets dominates `∑_{a ≤ z squarefree} 1/a`, which in turn is at least half the harmonic
sum, hence at least `(log z)/2`.
-/

namespace Brun

open Finset


lemma harmonic_le_two_mul_sum_sqfree (z : ℕ) :
    ∑ n ∈ Icc 1 z, (1 / (n : ℝ)) ≤ 2 * ∑ a ∈ sqfreeLE z, (1 / (a : ℝ)) := by
  classical
  set F : ℕ × ℕ → ℕ := fun q => q.1 * q.2 ^ 2 with hF
  have hsub : Icc 1 z ⊆ (sqfreeLE z ×ˢ Icc 1 z).image F := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    obtain ⟨a, b, hab, ha⟩ := Nat.sq_mul_squarefree n
    have hn0 : 0 < n := hn.1
    have hb0 : 0 < b := by
      rcases Nat.eq_zero_or_pos b with rfl | h
      · simp at hab; omega
      · exact h
    have ha0 : 0 < a := by
      rcases Nat.eq_zero_or_pos a with rfl | h
      · simp at hab; omega
      · exact h
    have haz : a ≤ z := by
      have : a ≤ n := by
        calc a ≤ b ^ 2 * a := Nat.le_mul_of_pos_left _ (by positivity)
        _ = n := hab
      omega
    have hbz : b ≤ z := by
      have : b ≤ n := by
        calc b ≤ b ^ 2 * a := by nlinarith
        _ = n := hab
      omega
    refine Finset.mem_image.mpr ⟨(a, b), ?_, ?_⟩
    · simp only [Finset.mem_product, sqfreeLE, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨⟨ha0, haz⟩, ha⟩, ⟨hb0, hbz⟩⟩
    · simp only [hF]
      omega
  calc ∑ n ∈ Icc 1 z, (1 / (n : ℝ))
      ≤ ∑ n ∈ (sqfreeLE z ×ˢ Icc 1 z).image F, (1 / (n : ℝ)) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
        intro i _ _; positivity
  _ ≤ ∑ q ∈ sqfreeLE z ×ˢ Icc 1 z, (1 / ((F q : ℕ) : ℝ)) := by
        refine Finset.sum_image_le _ _ _ ?_
        intro i _; positivity
  _ = (∑ a ∈ sqfreeLE z, (1 / (a : ℝ))) * ∑ b ∈ Icc 1 z, (1 / (b : ℝ) ^ 2) := by
        rw [Finset.sum_product, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        simp only [hF]
        push_cast
        rw [one_div, one_div, one_div, mul_inv]
  _ ≤ (∑ a ∈ sqfreeLE z, (1 / (a : ℝ))) * 2 := by
        have hnn : 0 ≤ ∑ a ∈ sqfreeLE z, (1 / (a : ℝ)) := by
          refine Finset.sum_nonneg (fun a _ => by positivity)
        exact mul_le_mul_of_nonneg_left (sum_inv_sq_le z) hnn
  _ = 2 * ∑ a ∈ sqfreeLE z, (1 / (a : ℝ)) := by ring

/-- The sum of reciprocals of squarefree numbers `≤ z` is dominated by the Euler product. -/
