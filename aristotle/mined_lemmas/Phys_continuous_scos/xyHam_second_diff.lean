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

lemma xyHam_second_diff (N : ℕ) (τ : Site d → Spin) (f : Site d → ℝ)
    (hsupp : ∀ x, x ∉ box d N → f x = 0) (θ : BoxCfg d N) :
    xyHam N τ (θ + shiftOf N f) + xyHam N τ (θ - shiftOf N f) - 2 * xyHam N τ θ
      ≤ ∑ x ∈ box d (N + 1), ∑ i : Fin d, (f x - f (x + unitVec i)) ^ 2 := by
  unfold xyHam
  refine sum_comb_le _ _ _ _ (fun x _ => ?_)
  refine sum_comb_le _ _ _ _ (fun i _ => ?_)
  set A : Spin := extend N τ θ x - extend N τ θ (x + unitVec i) with hA
  set t : ℝ := f x - f (x + unitVec i) with ht
  have hplus : extend N τ (θ + shiftOf N f) x - extend N τ (θ + shiftOf N f) (x + unitVec i)
      = A + (t : Spin) := by
    rw [extend_add_shift N τ f hsupp θ x, extend_add_shift N τ f hsupp θ (x + unitVec i), hA, ht,
      AddCircle.coe_sub]
    abel
  have hminus : extend N τ (θ - shiftOf N f) x - extend N τ (θ - shiftOf N f) (x + unitVec i)
      = A - (t : Spin) := by
    rw [extend_sub_shift N τ f hsupp θ x, extend_sub_shift N τ f hsupp θ (x + unitVec i), hA, ht,
      AddCircle.coe_sub]
    abel
  rw [hplus, hminus]
  have hid := scos_second_difference A t
  have hcos : 0 ≤ 1 - Real.cos t := by
    have := Real.cos_le_one t; linarith
  have hle : 2 * scos A * (1 - Real.cos t) ≤ 2 * (1 - Real.cos t) := by
    have h1 : scos A ≤ 1 := scos_le_one A
    nlinarith
  have hquad : 2 * (1 - Real.cos t) ≤ t ^ 2 := by
    have := one_sub_cos_le t; linarith
  have : (1 - scos (A + (t : Spin))) + (1 - scos (A - (t : Spin))) - 2 * (1 - scos A)
      = 2 * scos A - scos (A + (t : Spin)) - scos (A - (t : Spin)) := by ring
  rw [this, hid]
  linarith

/-- **Mermin–Wagner theorem.**  In dimension `d ≤ 2` and at any positive temperature
`T = 1/β > 0` the continuous rotation symmetry of the XY model is not spontaneously
broken: for every `ε > 0` there is a radius `R` such that for every box of radius
`N ≥ R` and every boundary condition `τ` outside that box, both components of the Gibbs
magnetisation at the origin are smaller than `ε` in absolute value. -/
