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

lemma HS_dirv_between {e f : E3} {a b c : ℝ} (hac : a ≤ c) (hcb : c ≤ b) (hab : b - a < π) :
    HS (dirv e f a) ∩ HS (dirv e f b) ⊆ HS (dirv e f c) := by
  rintro x ⟨hxa, hxb⟩
  simp only [mem_HS] at hxa hxb ⊢
  rcases eq_or_lt_of_le (hac.trans hcb) with hab' | hab'
  · -- degenerate: a = b, hence a = c = b
    have h1 : c = a := by linarith
    rw [h1]; exact hxa
  · have hsba : 0 < Real.sin (b - a) := Real.sin_pos_of_pos_of_lt_pi (by linarith) hab
    have hsbc : 0 ≤ Real.sin (b - c) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have hsca : 0 ≤ Real.sin (c - a) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have hid := dirv_comb e f a b c
    have : Real.sin (b - a) * ⟪x, dirv e f c⟫
        = Real.sin (b - c) * ⟪x, dirv e f a⟫ + Real.sin (c - a) * ⟪x, dirv e f b⟫ := by
      have := congrArg (fun y => ⟪x, y⟫) hid
      simpa [inner_add_right, real_inner_smul_right] using this
    nlinarith

