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

lemma dirv_comb (e f : E3) (a b c : ℝ) :
    Real.sin (b - a) • dirv e f c
      = Real.sin (b - c) • dirv e f a + Real.sin (c - a) • dirv e f b := by
  simp only [dirv, Real.sin_sub, smul_add, smul_smul]
  rw [show (Real.sin b * Real.cos a - Real.cos b * Real.sin a) * Real.cos c
      = (Real.sin b * Real.cos c - Real.cos b * Real.sin c) * Real.cos a
        + (Real.sin c * Real.cos a - Real.cos c * Real.sin a) * Real.cos b by ring,
    show (Real.sin b * Real.cos a - Real.cos b * Real.sin a) * Real.sin c
      = (Real.sin b * Real.cos c - Real.cos b * Real.sin c) * Real.sin a
        + (Real.sin c * Real.cos a - Real.cos c * Real.sin a) * Real.sin b by ring]
  module

/-- If `x` is on the positive side of the half-spaces at angles `a` and `b`, it is on the
positive side of every intermediate one. -/
