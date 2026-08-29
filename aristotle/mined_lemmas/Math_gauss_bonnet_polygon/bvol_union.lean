import Mathlib

/-!
# Additive monotone functions on an interval are linear

An elementary Cauchy-functional-equation argument: a nonnegative function on `[0, π]` which is
additive there is determined by its value at `π`.
-/

open scoped Real

namespace Math

variable {W : ℝ → ℝ}

/-- An additive nonnegative function is monotone. -/

lemma bvol_union (A B : Set E3) (hB : MeasurableSet B) (hnull : volume (A ∩ B) = 0) :
    bvol (A ∪ B) = bvol A + bvol B := by
  set C := closedBall (0 : E3) 1 with hC
  have h1 : C ∩ (A ∪ B) = (C ∩ A) ∪ (C ∩ B) := by
    rw [Set.inter_union_distrib_left]
  have h2 : volume ((C ∩ A) ∩ (C ∩ B)) = 0 := by
    refine measure_mono_null ?_ hnull
    rintro x ⟨⟨-, h1⟩, ⟨-, h2⟩⟩
    exact ⟨h1, h2⟩
  have key := measure_union_add_inter (μ := volume) (s := C ∩ A) (t := C ∩ B)
    (measurableSet_closedBall.inter hB)
  rw [← h1, h2, add_zero] at key
  rw [bvol, bvol, bvol, ← ENNReal.toReal_add (volume_ball_inter_ne_top A)
    (volume_ball_inter_ne_top B), key]

