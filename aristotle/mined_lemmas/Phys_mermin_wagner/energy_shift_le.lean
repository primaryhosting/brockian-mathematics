import Mathlib

/-!
# Core of the Mermin–Wagner argument

This file contains the model-independent part of the Mermin–Wagner theorem:
a finite collection of classical `O(2)` spins with an arbitrary nonnegative,
rotation-invariant pair interaction, plus arbitrary single-site terms
(boundary conditions / external fields).

The main result `Phys.abs_magnetization_le` bounds the magnetization at a
distinguished site `o` by the *Dirichlet energy* of any "spin wave" profile
`a : V → ℝ` which equals `π` at `o` and vanishes wherever a single-site term
is present.
-/

open MeasureTheory

noncomputable instance factTwoPi : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The state space of a single classical `O(2)` (planar rotator) spin. -/
abbrev Spin := AddCircle (2 * Real.pi)

namespace Phys

section Trig


theorem energy_shift_le (J : V → V → ℝ) (hJ : ∀ x y, 0 ≤ J x y) (G : V → Spin → ℝ)
    (a : V → ℝ) (hGa : ∀ x, a x ≠ 0 → G x = 0) (θ : V → Spin) :
    energy J G (θ + fun x => ((a x : ℝ) : Spin)) + energy J G (θ - fun x => ((a x : ℝ) : Spin))
      - 2 * energy J G θ ≤ dirichlet J a := by
  set sa : V → Spin := fun x => ((a x : ℝ) : Spin) with hsa
  -- single site terms are unchanged
  have hGterm : ∀ x, G x ((θ + sa) x) + G x ((θ - sa) x) - 2 * G x (θ x) = 0 := by
    intro x
    by_cases hx : a x = 0
    · have hz : sa x = 0 := by simp [hsa, hx]
      simp only [Pi.add_apply, Pi.sub_apply, hz, add_zero, sub_zero]; ring
    · simp [hGa x hx]
  have hdiff : ∀ x y, (θ + sa) x - (θ + sa) y = (θ x - θ y) + ((a x - a y : ℝ) : Spin) := by
    intro x y
    show (θ x + sa x) - (θ y + sa y) = _
    rw [AddCircle.coe_sub]
    abel
  have hdiff' : ∀ x y, (θ - sa) x - (θ - sa) y = (θ x - θ y) - ((a x - a y : ℝ) : Spin) := by
    intro x y
    show (θ x - sa x) - (θ y - sa y) = _
    rw [AddCircle.coe_sub]
    abel
  have key : ∀ x y, -(J x y * Real.Angle.cos ((θ + sa) x - (θ + sa) y)
      + J x y * Real.Angle.cos ((θ - sa) x - (θ - sa) y)
      - 2 * (J x y * Real.Angle.cos (θ x - θ y))) ≤ J x y * (a x - a y) ^ 2 := by
    intro x y
    rw [hdiff x y, hdiff' x y]
    have h := cos_shift_estimate (θ x - θ y) (a x - a y)
    calc -(J x y * Real.Angle.cos (θ x - θ y + ((a x - a y : ℝ) : Spin))
            + J x y * Real.Angle.cos (θ x - θ y - ((a x - a y : ℝ) : Spin))
            - 2 * (J x y * Real.Angle.cos (θ x - θ y)))
        = J x y * -(Real.Angle.cos (θ x - θ y + ((a x - a y : ℝ) : Spin))
            + Real.Angle.cos (θ x - θ y - ((a x - a y : ℝ) : Spin))
            - 2 * Real.Angle.cos (θ x - θ y)) := by ring
      _ ≤ J x y * (a x - a y) ^ 2 := mul_le_mul_of_nonneg_left h (hJ x y)
  have hT : (∑ x, G x ((θ + sa) x)) + (∑ x, G x ((θ - sa) x)) - 2 * (∑ x, G x (θ x)) = 0 := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_eq_zero fun x _ => hGterm x
  have hS : (∑ x, ∑ y, J x y * Real.Angle.cos ((θ + sa) x - (θ + sa) y))
      + (∑ x, ∑ y, J x y * Real.Angle.cos ((θ - sa) x - (θ - sa) y))
      - 2 * (∑ x, ∑ y, J x y * Real.Angle.cos (θ x - θ y))
      = ∑ x, ∑ y, (J x y * Real.Angle.cos ((θ + sa) x - (θ + sa) y)
          + J x y * Real.Angle.cos ((θ - sa) x - (θ - sa) y)
          - 2 * (J x y * Real.Angle.cos (θ x - θ y))) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
  unfold energy dirichlet
  have expand : ∀ A B C P Q R : ℝ,
      (-A + P) + (-B + Q) - 2 * (-C + R) = -(A + B - 2 * C) + (P + Q - 2 * R) := by
    intro A B C P Q R; ring
  rw [expand, hT, add_zero, hS, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_le_sum fun y _ => key x y

/-! ### The Gibbs state -/

/-- Translation invariance of the reference measure. -/
