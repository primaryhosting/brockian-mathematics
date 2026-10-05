import Mathlib

/-!
# The circle-valued spin space

The spin space of the classical XY model is the circle `Spin = ℝ / 2πℤ`, a compact
abelian group carrying a translation invariant (Haar) measure.  This file sets up the
cosine and sine functions on `Spin` together with the elementary trigonometric facts
used in the Mermin–Wagner argument.
-/

namespace Phys

noncomputable section

open MeasureTheory

instance factTwoPi : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The spin space: the circle `ℝ / 2πℤ`. -/
abbrev Spin := AddCircle (2 * Real.pi)

/-- The cosine function on the circle. -/

lemma dirichletEnergy_le (hd : d ≤ 2) {R N : ℕ} (hR : 1 ≤ R) (hN : R ≤ N) :
    dirichletEnergy (d := d) R N
      ≤ (18 + 16 * Real.log (1 + (R : ℝ))) / (Real.log (1 + (R : ℝ))) ^ 2 := by
  classical
  have hL : 0 < Real.log (1 + (R:ℝ)) := by
    apply Real.log_pos
    have : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
    linarith
  have hA : dirichletEnergy (d := d) R N
      = ∑ x ∈ box d (R + 1), ∑ i : Fin d, (spinWave R x - spinWave R (x + unitVec i)) ^ 2 := by
    unfold dirichletEnergy
    refine (Finset.sum_subset (box_subset (by omega)) ?_).symm
    intro x hx hnx
    rw [mem_box_iff] at hnx
    refine Finset.sum_eq_zero (fun i _ => ?_)
    have e1 : spinWave R x = 0 := spinWave_eq_zero_of_le hR (by omega)
    have e2 : spinWave R (x + unitVec i) = 0 := by
      refine spinWave_eq_zero_of_le hR ?_
      have := snorm_le_snorm_add_unit x i
      omega
    rw [e1, e2]; ring
  rw [hA]
  have hB : ∀ x ∈ box d (R + 1),
      ∑ i : Fin d, (spinWave R x - spinWave R (x + unitVec i)) ^ 2
        ≤ (2 / Real.log (1 + (R:ℝ)) ^ 2) * (1 / (max (snorm x : ℝ) 1) ^ 2) := by
    intro x _
    have hm : (0:ℝ) < max (snorm x : ℝ) 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have hterm : ∀ i : Fin d, (spinWave R x - spinWave R (x + unitVec i)) ^ 2
        ≤ 1 / ((max (snorm x : ℝ) 1) ^ 2 * Real.log (1 + (R:ℝ)) ^ 2) := by
      intro i
      have h1 := spinWave_grad_bound (d := d) hR x i
      have h2 : (spinWave R x - spinWave R (x + unitVec i)) ^ 2
          = |spinWave R x - spinWave R (x + unitVec i)| ^ 2 := (sq_abs _).symm
      rw [h2]
      calc |spinWave R x - spinWave R (x + unitVec i)| ^ 2
          ≤ (1 / ((max (snorm x : ℝ) 1) * Real.log (1 + (R:ℝ)))) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) h1 2
        _ = 1 / ((max (snorm x : ℝ) 1) ^ 2 * Real.log (1 + (R:ℝ)) ^ 2) := by
            rw [div_pow, one_pow, mul_pow]
    calc ∑ i : Fin d, (spinWave R x - spinWave R (x + unitVec i)) ^ 2
        ≤ ∑ _i : Fin d, 1 / ((max (snorm x : ℝ) 1) ^ 2 * Real.log (1 + (R:ℝ)) ^ 2) :=
          Finset.sum_le_sum (fun i _ => hterm i)
      _ = (d : ℝ) * (1 / ((max (snorm x : ℝ) 1) ^ 2 * Real.log (1 + (R:ℝ)) ^ 2)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ 2 * (1 / ((max (snorm x : ℝ) 1) ^ 2 * Real.log (1 + (R:ℝ)) ^ 2)) := by
          have hd' : (d:ℝ) ≤ 2 := by exact_mod_cast hd
          have hnn : (0:ℝ) ≤ 1 / ((max (snorm x : ℝ) 1) ^ 2 * Real.log (1 + (R:ℝ)) ^ 2) := by
            positivity
          nlinarith
      _ = (2 / Real.log (1 + (R:ℝ)) ^ 2) * (1 / (max (snorm x : ℝ) 1) ^ 2) := by
          field_simp
  calc ∑ x ∈ box d (R + 1), ∑ i : Fin d, (spinWave R x - spinWave R (x + unitVec i)) ^ 2
      ≤ ∑ x ∈ box d (R + 1),
          (2 / Real.log (1 + (R:ℝ)) ^ 2) * (1 / (max (snorm x : ℝ) 1) ^ 2) :=
        Finset.sum_le_sum hB
    _ = (2 / Real.log (1 + (R:ℝ)) ^ 2) * ∑ x ∈ box d (R + 1), 1 / (max (snorm x : ℝ) 1) ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ (2 / Real.log (1 + (R:ℝ)) ^ 2) * (9 + 8 * Real.log (1 + (R:ℝ))) :=
        mul_le_mul_of_nonneg_left (shell_sum_bound hd R) (by positivity)
    _ = (18 + 16 * Real.log (1 + (R : ℝ))) / (Real.log (1 + (R : ℝ))) ^ 2 := by
        field_simp
        ring

/-- **Vanishing Dirichlet energy in dimension `d ≤ 2`.**  For every `ε > 0` there is a
spin wave, equal to `1` at the origin and supported in a finite box, whose Dirichlet
energy is smaller than `ε`. -/
