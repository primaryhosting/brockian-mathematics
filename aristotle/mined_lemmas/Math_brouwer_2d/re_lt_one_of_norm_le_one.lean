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

set_option grind.warning false

namespace Math

open Complex Metric Set

/-- If `u` lies in the closed unit disk of `ℂ` and `u ≠ 1`, then `u.re < 1`. -/

lemma re_lt_one_of_norm_le_one {u : ℂ} (hu : ‖u‖ ≤ 1) (h1 : u ≠ 1) : u.re < 1 := by
  rcases lt_or_eq_of_le (le_trans (Complex.re_le_norm u) hu) with h | h
  · exact h
  · exfalso
    apply h1
    have hn : u.re ^ 2 + u.im ^ 2 ≤ 1 := by
      have h2 : ‖u‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg u]
      have := Complex.normSq_eq_norm_sq u
      rw [Complex.normSq_apply] at this
      nlinarith [this]
    have him : u.im = 0 := by nlinarith
    apply Complex.ext <;> simp [h, him]

/-- There is no continuous `φ : ℝ → ℝ` whose cosine is everywhere positive and which
decreases by exactly `2π` between `0` and `2π`. -/
