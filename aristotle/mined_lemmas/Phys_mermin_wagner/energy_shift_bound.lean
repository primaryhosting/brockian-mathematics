/-
Classical `XY`-type models with a continuous (rotation) symmetry, and the
Mermin–Wagner / Pfister "two–shift" bound on the magnetization in terms of the
Dirichlet energy of a cut-off function.
-/
import Mathlib

open MeasureTheory Real

noncomputable section

namespace MerminWagner

instance factTwoPi : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The spin space: the circle `ℝ / 2πℤ`.  The continuous symmetry group of the
models below is the rotation group of this circle acting diagonally on all spins. -/
abbrev Spin : Type := AddCircle (2 * Real.pi)

/-- The cosine function on the circle. -/

lemma energy_shift_bound (hJ : ∀ x y, 0 ≤ J x y) (hbf : ∀ x, f x ≠ 0 → b x = 0)
    (θ : V → Spin) :
    energy J b (θ + shift f) + energy J b (θ - shift f)
      ≤ 2 * energy J b θ + Real.pi ^ 2 * dirichletEnergy J f := by
  have hb : ∀ x, b x ((θ + shift f) x) + b x ((θ - shift f) x) - 2 * b x (θ x) = 0 := by
    intro x
    by_cases hfx : f x = 0
    · have : shift f x = (0 : Spin) := by
        simp [shift, hfx]
      simp [this]
    · simp [hbf x hfx]
  have hpair : ∀ x y,
      -(J x y * scos ((θ + shift f) x - (θ + shift f) y))
        - J x y * scos ((θ - shift f) x - (θ - shift f) y)
        + 2 * (J x y * scos (θ x - θ y))
      ≤ J x y * (Real.pi ^ 2 * (f x - f y) ^ 2) := by
    intro x y
    set d : Spin := θ x - θ y with hd
    set t : ℝ := Real.pi * (f x - f y) with ht
    have e1 : (θ + shift f) x - (θ + shift f) y = d + (t : Spin) := by
      simp only [Pi.add_apply, shift, hd, ht]
      push_cast
      ring
    have e2 : (θ - shift f) x - (θ - shift f) y = d - (t : Spin) := by
      simp only [Pi.sub_apply, shift, hd, ht]
      push_cast
      ring
    rw [e1, e2]
    have key : scos (d + (t : Spin)) + scos (d - (t : Spin)) = 2 * scos d * Real.cos t :=
      scos_add_add_sub d t
    have hcos : 1 - Real.cos t ≤ t ^ 2 / 2 := by
      have := Real.one_sub_sq_div_two_le_cos (x := t)
      linarith
    have hcos1 : Real.cos t ≤ 1 := Real.cos_le_one t
    have hsd : scos d ≤ 1 := scos_le_one d
    have hJxy := hJ x y
    have expand :
        -(J x y * scos (d + (t : Spin))) - J x y * scos (d - (t : Spin))
          + 2 * (J x y * scos d)
          = 2 * J x y * scos d * (1 - Real.cos t) := by
      have : J x y * scos (d + (t : Spin)) + J x y * scos (d - (t : Spin))
          = J x y * (2 * scos d * Real.cos t) := by rw [← mul_add, key]
      nlinarith [this]
    rw [expand]
    have h1 : 2 * J x y * scos d * (1 - Real.cos t) ≤ 2 * J x y * (1 - Real.cos t) := by
      have h0 : 0 ≤ 1 - Real.cos t := by linarith
      nlinarith
    have h2 : 2 * J x y * (1 - Real.cos t) ≤ J x y * t ^ 2 := by nlinarith
    have h3 : J x y * t ^ 2 = J x y * (Real.pi ^ 2 * (f x - f y) ^ 2) := by
      rw [ht]; ring
    linarith
  have hsum :
      (∑ x, ∑ y, (-(J x y * scos ((θ + shift f) x - (θ + shift f) y))
        - J x y * scos ((θ - shift f) x - (θ - shift f) y)
        + 2 * (J x y * scos (θ x - θ y))))
        ≤ ∑ x, ∑ y, J x y * (Real.pi ^ 2 * (f x - f y) ^ 2) :=
    Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hpair x y
  have hbsum : ∑ x, (b x ((θ + shift f) x) + b x ((θ - shift f) x) - 2 * b x (θ x)) = 0 :=
    Finset.sum_eq_zero fun x _ => hb x
  have hD : ∑ x, ∑ y, J x y * (Real.pi ^ 2 * (f x - f y) ^ 2)
      = Real.pi ^ 2 * dirichletEnergy J f := by
    unfold dirichletEnergy
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  unfold energy
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at *
  nlinarith [hsum, hbsum, hD]

end MainBound

end MerminWagner

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

