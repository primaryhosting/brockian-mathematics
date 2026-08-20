/-
The classical XY model on a finite graph, and the finite-volume Mermin-Wagner bound
on its magnetization in terms of the Dirichlet energy of a spin-wave profile.
-/
import RequestProject.Core

open MeasureTheory Real

namespace Phys

noncomputable section

variable {S ι : Type} [Fintype S]

/-- The energy of the classical XY model on a finite graph whose edges are indexed by
`bonds`, with endpoints `src` and `tgt`, coupling `J` and external field `h`. -/

lemma sum_bnd_le {R : ℕ} (hR : 1 ≤ R) :
    ∑ m ∈ Finset.range (R + 1), (12 * m + 1 : ℝ) * bnd R m ≤ 96 / harm R := by
  have hH := harm_pos hR
  have hH1 := one_le_harm hR
  have hstep : ∀ m ∈ Finset.range (R + 1),
      (12 * m + 1 : ℝ) * bnd R m ≤ 48 / (((m : ℝ) + 1) * harm R ^ 2) := by
    intro m hm
    simp only [Finset.mem_range] at hm
    unfold bnd
    rw [if_pos (by omega : m ≤ R)]
    have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hsq : (2 / (((m : ℝ) + 1) * harm R)) ^ 2 = 4 / (((m : ℝ) + 1) ^ 2 * harm R ^ 2) := by
      rw [div_pow]
      norm_num [mul_pow]
    rw [hsq, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : (12 * (m : ℝ) + 1) * 4 ≤ 48 * ((m : ℝ) + 1) := by linarith
    have h2 : (0 : ℝ) ≤ ((m : ℝ) + 1) * harm R ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right h1 h2]
  refine le_trans (Finset.sum_le_sum hstep) ?_
  have hEq : ∑ m ∈ Finset.range (R + 1), 48 / (((m : ℝ) + 1) * harm R ^ 2)
      = (48 / harm R ^ 2) * harm (R + 1) := by
    unfold harm
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    field_simp
  rw [hEq]
  have hharm : harm (R + 1) ≤ 2 * harm R := by
    rw [harm_succ]
    have : 1 / ((R : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg R
      linarith
    linarith
  have hpos : (0 : ℝ) < 48 / harm R ^ 2 := by positivity
  calc (48 / harm R ^ 2) * harm (R + 1) ≤ (48 / harm R ^ 2) * (2 * harm R) :=
        mul_le_mul_of_nonneg_left hharm hpos.le
    _ = 96 / harm R := by field_simp; ring

/-- **Dirichlet energy of the spin-wave profile.**  In dimension `d ≤ 2` it is
`O(1 / harm R)`, hence tends to `0` as `R → ∞`: this is exactly where `d ≤ 2` enters. -/
