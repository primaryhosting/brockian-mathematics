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

theorem sqNorm_bound {d L R : ℕ} (hd : d ≤ 2) (hR : 1 ≤ R) :
    sqNorm (swProfile d L R) ≤ Real.pi ^ 2 * 13 * ((R : ℝ) + 1) ^ 2 := by
  have hpi : (0 : ℝ) ≤ Real.pi ^ 2 := sq_nonneg _
  have hRnn : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg R
  have hstep : sqNorm (swProfile d L R)
      = Real.pi ^ 2 * ∑ x : Site d L, (prof R (rad x)) ^ 2 := by
    unfold sqNorm swProfile
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  have hshell : ∑ x : Site d L, (prof R (rad x)) ^ 2
      ≤ ∑ m ∈ Finset.range (L + 1), (12 * m + 1 : ℝ) * (prof R m) ^ 2 :=
    sum_shell_le hd (fun m => (prof R m) ^ 2) (fun _ => sq_nonneg _)
  have hcut : ∑ m ∈ Finset.range (L + 1), (12 * m + 1 : ℝ) * (prof R m) ^ 2
      ≤ 13 * ((R : ℝ) + 1) ^ 2 := by
    have hTsub : Finset.range (L + 1) ∩ Finset.range (R + 1) ⊆ Finset.range (L + 1) :=
      Finset.inter_subset_left
    have hvanish : ∀ m ∈ Finset.range (L + 1), m ∉ Finset.range (L + 1) ∩ Finset.range (R + 1) →
        (12 * m + 1 : ℝ) * (prof R m) ^ 2 = 0 := by
      intro m hm hmT
      have hmR : ¬ m < R + 1 := fun hlt =>
        hmT (Finset.mem_inter.mpr ⟨hm, Finset.mem_range.mpr hlt⟩)
      have : prof R m = 0 := prof_eq_zero_of_le hR (by omega)
      rw [this]
      ring
    rw [← Finset.sum_subset hTsub hvanish]
    have hterm : ∀ m ∈ Finset.range (L + 1) ∩ Finset.range (R + 1),
        (12 * m + 1 : ℝ) * (prof R m) ^ 2 ≤ 12 * (R : ℝ) + 1 := by
      intro m hm
      have hmR : m ≤ R := by
        have := (Finset.mem_inter.mp hm).2
        simp only [Finset.mem_range] at this
        omega
      have hmR' : (m : ℝ) ≤ (R : ℝ) := by exact_mod_cast hmR
      have h0 := prof_nonneg R m
      have h1 := prof_le_one R m
      have hp2 : prof R m ^ 2 ≤ 1 := by nlinarith
      have hcoef : (0 : ℝ) ≤ 12 * (m : ℝ) + 1 := by positivity
      calc (12 * (m : ℝ) + 1) * prof R m ^ 2 ≤ (12 * (m : ℝ) + 1) * 1 :=
            mul_le_mul_of_nonneg_left hp2 hcoef
        _ ≤ 12 * (R : ℝ) + 1 := by linarith
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : ((Finset.range (L + 1) ∩ Finset.range (R + 1)).card : ℝ) ≤ (R : ℝ) + 1 := by
      have : (Finset.range (L + 1) ∩ Finset.range (R + 1)).card ≤ R + 1 := by
        calc (Finset.range (L + 1) ∩ Finset.range (R + 1)).card
            ≤ (Finset.range (R + 1)).card := Finset.card_le_card Finset.inter_subset_right
          _ = R + 1 := Finset.card_range _
      exact_mod_cast this
    nlinarith [hcard]
  rw [hstep]
  nlinarith [hshell.trans hcut, hpi]

/-- Sanity check: the magnetization is an average of `cos`, hence lies in `[-1, 1]`. -/
