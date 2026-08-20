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

theorem dirichlet_bound {d L R : ℕ} (hd : d ≤ 2) (hR : 1 ≤ R) :
    dirichlet (bondSet d L) bsrc btgt (swProfile d L R) ≤ Real.pi ^ 2 * 192 / harm R := by
  have hH := harm_pos hR
  have hstep : ∀ p ∈ bondSet d L,
      (swProfile d L R (bsrc p) - swProfile d L R (btgt p)) ^ 2
        ≤ Real.pi ^ 2 * bnd R (rad p.1) := by
    intro p hp
    obtain ⟨h1, h2⟩ := rad_btgt_close hp
    unfold swProfile bsrc
    rw [← mul_sub, mul_pow]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    by_cases hcase : rad p.1 ≤ R
    · unfold bnd
      rw [if_pos hcase]
      have habs := prof_diff_le (R := R) hR (a := rad p.1) (b := rad (btgt p)) h1 h2
      have hmax : (((rad p.1 : ℝ) + 1) * harm R) / 2 ≤ ((max (rad p.1) 1 : ℕ) : ℝ) * harm R := by
        have hm : ((rad p.1 : ℝ) + 1) / 2 ≤ ((max (rad p.1) 1 : ℕ) : ℝ) := by
          rcases Nat.eq_zero_or_pos (rad p.1) with h0 | h0
          · rw [h0]
            norm_num
          · have : (max (rad p.1) 1 : ℕ) = rad p.1 := by omega
            rw [this]
            have : (1 : ℝ) ≤ (rad p.1 : ℝ) := by exact_mod_cast h0
            linarith
        calc (((rad p.1 : ℝ) + 1) * harm R) / 2 = (((rad p.1 : ℝ) + 1) / 2) * harm R := by ring
          _ ≤ ((max (rad p.1) 1 : ℕ) : ℝ) * harm R := mul_le_mul_of_nonneg_right hm hH.le
      have hpos : (0 : ℝ) < (((rad p.1 : ℝ) + 1) * harm R) / 2 := by positivity
      have hle2 : 1 / (((max (rad p.1) 1 : ℕ) : ℝ) * harm R)
          ≤ 2 / (((rad p.1 : ℝ) + 1) * harm R) := by
        rw [div_le_div_iff₀ (by linarith [hpos, hmax]) (by positivity)]
        linarith [hmax]
      calc (prof R (rad p.1) - prof R (rad (btgt p))) ^ 2
          = |prof R (rad p.1) - prof R (rad (btgt p))| ^ 2 := (sq_abs _).symm
        _ ≤ (2 / (((rad p.1 : ℝ) + 1) * harm R)) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) (le_trans habs hle2) 2
    · push_neg at hcase
      have hz1 : prof R (rad p.1) = 0 := prof_eq_zero_of_le hR (le_of_lt hcase)
      have hz2 : prof R (rad (btgt p)) = 0 := prof_eq_zero_of_le hR (by omega)
      rw [hz1, hz2]
      simpa using bnd_nonneg R (rad p.1)
  have hsum1 : dirichlet (bondSet d L) bsrc btgt (swProfile d L R)
      ≤ ∑ p ∈ bondSet d L, Real.pi ^ 2 * bnd R (rad p.1) :=
    Finset.sum_le_sum hstep
  have hsum2 : ∑ p ∈ bondSet d L, Real.pi ^ 2 * bnd R (rad p.1)
      ≤ ∑ p : Site d L × Fin d, Real.pi ^ 2 * bnd R (rad p.1) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
    intro p _ _
    have := bnd_nonneg R (rad p.1)
    positivity
  have hsum3 : ∑ p : Site d L × Fin d, Real.pi ^ 2 * bnd R (rad p.1)
      = (d : ℝ) * (Real.pi ^ 2 * ∑ x : Site d L, bnd R (rad x)) := by
    rw [Fintype.sum_prod_type]
    have hin : ∀ x : Site d L, ∑ _y : Fin d, Real.pi ^ 2 * bnd R (rad x)
        = (d : ℝ) * (Real.pi ^ 2 * bnd R (rad x)) := by
      intro x
      rw [Finset.sum_const, nsmul_eq_mul]
      simp
    rw [Finset.sum_congr rfl fun x _ => hin x, ← Finset.mul_sum, ← Finset.mul_sum]
  have hsum4 : ∑ x : Site d L, bnd R (rad x)
      ≤ ∑ m ∈ Finset.range (L + 1), (12 * m + 1 : ℝ) * bnd R m :=
    sum_shell_le hd (bnd R) (bnd_nonneg R)
  have hsum5 : ∑ m ∈ Finset.range (L + 1), (12 * m + 1 : ℝ) * bnd R m ≤ 96 / harm R := by
    have hTsub : Finset.range (L + 1) ∩ Finset.range (R + 1) ⊆ Finset.range (L + 1) :=
      Finset.inter_subset_left
    have hvanish : ∀ m ∈ Finset.range (L + 1), m ∉ Finset.range (L + 1) ∩ Finset.range (R + 1) →
        (12 * m + 1 : ℝ) * bnd R m = 0 := by
      intro m hm hmT
      have hmR : ¬ m < R + 1 := fun hlt =>
        hmT (Finset.mem_inter.mpr ⟨hm, Finset.mem_range.mpr hlt⟩)
      unfold bnd
      rw [if_neg (by omega)]
      ring
    rw [← Finset.sum_subset hTsub hvanish]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right ?_)
      (sum_bnd_le hR)
    intro m _ _
    have := bnd_nonneg R m
    positivity
  have hd' : (d : ℝ) ≤ 2 := by exact_mod_cast hd
  have hbnn : 0 ≤ ∑ x : Site d L, bnd R (rad x) :=
    Finset.sum_nonneg fun x _ => bnd_nonneg R (rad x)
  have hpi : (0 : ℝ) ≤ Real.pi ^ 2 := sq_nonneg _
  have hfin : ∑ x : Site d L, bnd R (rad x) ≤ 96 / harm R := hsum4.trans hsum5
  calc dirichlet (bondSet d L) bsrc btgt (swProfile d L R)
      ≤ (d : ℝ) * (Real.pi ^ 2 * ∑ x : Site d L, bnd R (rad x)) := by
        rw [← hsum3]; exact hsum1.trans hsum2
    _ ≤ 2 * (Real.pi ^ 2 * (96 / harm R)) := by
        have h1 : Real.pi ^ 2 * ∑ x : Site d L, bnd R (rad x) ≤ Real.pi ^ 2 * (96 / harm R) :=
          mul_le_mul_of_nonneg_left hfin hpi
        have h2 : (0 : ℝ) ≤ Real.pi ^ 2 * (96 / harm R) := by positivity
        nlinarith [mul_nonneg hpi hbnn]
    _ = Real.pi ^ 2 * 192 / harm R := by ring

/-- The `ℓ²` norm of the spin-wave profile is controlled by the volume of the ball of
radius `R`. -/
