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

lemma additive_nsmul (hzero : W 0 = 0)
    (hadd : ∀ x y : ℝ, 0 < x → 0 < y → x + y ≤ π → W (x + y) = W x + W y) :
    ∀ (n : ℕ) (x : ℝ), 0 < x → (n : ℝ) * x ≤ π → W ((n : ℝ) * x) = n * W x := by
  intro n
  induction n with
  | zero => intro x _ _; simpa using hzero
  | succ n ih =>
    intro x hx hle
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hnx : (0 : ℝ) < (n : ℝ) * x := by positivity
      have hcast : ((n + 1 : ℕ) : ℝ) * x = (n : ℝ) * x + x := by push_cast; ring
      rw [hcast] at hle ⊢
      rw [hadd ((n : ℝ) * x) x hnx hx hle, ih x hx (by linarith)]
      push_cast
      ring

/-- A nonnegative additive function on `[0, π]` with `W π = 2π/3` is `θ ↦ 2θ/3`. -/
