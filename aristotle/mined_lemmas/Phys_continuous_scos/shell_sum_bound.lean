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

lemma shell_sum_bound (hd : d ≤ 2) (R : ℕ) :
    ∑ x ∈ box d (R + 1), 1 / (max (snorm x : ℝ) 1) ^ 2 ≤ 9 + 8 * Real.log (1 + (R:ℝ)) := by
  classical
  set W : Site d → ℝ := fun x => 1 / (max (snorm x : ℝ) 1) ^ 2 with hW
  have hmaps : ∀ x ∈ box d (R + 1), snorm x ∈ Finset.range (R + 2) := by
    intro x hx
    rw [mem_box_iff] at hx
    simp only [Finset.mem_range]
    omega
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps W
  rw [← hfib]
  have hfiber : ∀ r ∈ Finset.range (R + 2),
      ∑ x ∈ (box d (R + 1)).filter (fun x => snorm x = r), W x
        = ((box d (R + 1)).filter (fun x => snorm x = r)).card * (1 / (max (r:ℝ) 1) ^ 2) := by
    intro r _
    rw [Finset.sum_congr rfl (fun x hx => ?_), Finset.sum_const, nsmul_eq_mul]
    simp only [Finset.mem_filter] at hx
    rw [hW]
    simp [hx.2]
  rw [Finset.sum_congr rfl hfiber, Finset.sum_range_succ']
  have h0 : (((box d (R + 1)).filter (fun x => snorm x = 0)).card : ℝ) * (1 / (max (0:ℝ) 1) ^ 2)
      ≤ 1 := by
    have hsub : ((box d (R + 1)).filter (fun x => snorm x = 0)) ⊆ box d 0 := by
      intro x hx
      simp only [Finset.mem_filter] at hx
      rw [mem_box_iff, hx.2]
    have hc : (((box d (R + 1)).filter (fun x => snorm x = 0)).card : ℝ) ≤ 1 := by
      have hcc := Finset.card_le_card hsub
      rw [card_box] at hcc
      simp at hcc
      exact_mod_cast hcc
    have hone : (1:ℝ) / (max (0:ℝ) 1) ^ 2 = 1 := by norm_num
    rw [hone, mul_one]
    exact hc
  have hstep : ∀ i ∈ Finset.range (R + 1),
      (((box d (R + 1)).filter (fun x => snorm x = i + 1)).card : ℝ)
        * (1 / (max ((i:ℝ) + 1) 1) ^ 2) ≤ 8 / ((i:ℝ) + 1) := by
    intro i _
    have hcard : (((box d (R + 1)).filter (fun x => snorm x = i + 1)).card : ℝ)
        ≤ 8 * ((i:ℝ) + 1) := by
      have hc := card_shell_le (d := d) hd (R + 1) (i + 1) (by omega)
      have h2 : (((box d (R + 1)).filter (fun x => snorm x = i + 1)).card : ℝ)
          ≤ ((8 * (i + 1) : ℕ) : ℝ) := by exact_mod_cast hc
      push_cast at h2
      linarith
    have hmax : max ((i:ℝ) + 1) 1 = (i:ℝ) + 1 := by
      apply max_eq_left
      have : (0:ℝ) ≤ (i:ℝ) := Nat.cast_nonneg _
      linarith
    rw [hmax]
    have hpos : (0:ℝ) < (i:ℝ) + 1 := by positivity
    rw [mul_one_div, div_le_div_iff₀ (by positivity) hpos]
    nlinarith [hcard, hpos]
  have hsum : ∑ i ∈ Finset.range (R + 1),
      (((box d (R + 1)).filter (fun x => snorm x = i + 1)).card : ℝ)
        * (1 / (max ((i:ℝ) + 1) 1) ^ 2)
      ≤ ∑ i ∈ Finset.range (R + 1), 8 / ((i:ℝ) + 1) := Finset.sum_le_sum hstep
  have hharm : ∑ i ∈ Finset.range (R + 1), 8 / ((i:ℝ) + 1) ≤ 8 * (1 + Real.log (1 + (R:ℝ))) := by
    have h := harmonic_le_one_add_log (R + 1)
    have hcast : ((harmonic (R + 1) : ℚ) : ℝ) = ∑ i ∈ Finset.range (R + 1), (1:ℝ) / (i + 1) := by
      rw [harmonic]
      push_cast
      simp [one_div]
    rw [hcast] at h
    have hlog : Real.log ((R + 1 : ℕ) : ℝ) = Real.log (1 + (R:ℝ)) := by
      congr 1
      push_cast
      ring
    rw [hlog] at h
    have heq : ∑ i ∈ Finset.range (R + 1), 8 / ((i:ℝ) + 1)
        = 8 * ∑ i ∈ Finset.range (R + 1), (1:ℝ) / (i + 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    rw [heq]
    linarith
  have heq2 : ∀ i : ℕ, (max (((i + 1 : ℕ)):ℝ) 1) = max ((i:ℝ) + 1) 1 := by
    intro i; push_cast; ring_nf
  simp only [heq2, Nat.cast_zero]
  linarith [hsum.trans hharm, h0]

/-- The Dirichlet energy of the logarithmic spin wave is `O(1 / log R)`. -/
