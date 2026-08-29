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

lemma bvol_split (S : Set E3) (hS : MeasurableSet S) {n : E3} (hn : n ≠ 0) :
    bvol S = bvol (S ∩ HS n) + bvol (S ∩ HS (-n)) := by
  set B := closedBall (0 : E3) 1 with hB
  have hmeas : MeasurableSet (B ∩ S ∩ HS (-n)) :=
    ((measurableSet_closedBall.inter hS).inter (measurableSet_HS _))
  have hunion : (B ∩ S ∩ HS n) ∪ (B ∩ S ∩ HS (-n)) = B ∩ S := by
    ext x
    simp only [Set.mem_union, Set.mem_inter_iff, mem_HS, inner_neg_right]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h
      rcases le_total 0 ⟪x, n⟫ with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr ⟨h, by linarith⟩
  have hinter : volume ((B ∩ S ∩ HS n) ∩ (B ∩ S ∩ HS (-n))) = 0 := by
    refine measure_mono_null ?_ (hyperplane_null hn)
    rintro x ⟨⟨-, h1⟩, ⟨-, h2⟩⟩
    simp only [mem_HS, inner_neg_right] at h1 h2
    exact le_antisymm (by linarith) h1
  have key := measure_union_add_inter (μ := volume) (B ∩ S ∩ HS n) hmeas
  rw [hunion, hinter, add_zero] at key
  have h1 := volume_ball_inter_ne_top (S ∩ HS n)
  have h2 := volume_ball_inter_ne_top (S ∩ HS (-n))
  simp only [bvol, ← Set.inter_assoc]
  rw [← ENNReal.toReal_add (by rw [Set.inter_assoc]; exact h1) (by rw [Set.inter_assoc]; exact h2),
    key]

