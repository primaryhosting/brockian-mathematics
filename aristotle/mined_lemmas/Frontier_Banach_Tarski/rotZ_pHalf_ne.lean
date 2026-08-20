import RequestProject.BT.Ball

/-!
# Banach Tarski
Category: Frontier — Set Theory
Target: Frontier.Banach_Tarski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Metric Set
open scoped Pointwise

namespace Frontier

/-- The vector by which the second copy of the ball is translated. -/

theorem rotZ_pHalf_ne (n : ℕ) (hn : 0 < n) :
    (rotZ (Real.cos (n * 1)) (Real.sin (n * 1)) (Real.cos_sq_add_sin_sq _)) pHalf ≠ pHalf := by
  intro h
  have h0 : Real.cos (n * 1) * (1 / 2) - Real.sin (n * 1) * 0 = 1 / 2 := by
    have := congrArg (fun v : E => v 0) h
    simpa [pHalf] using this
  have hcos : Real.cos (n : ℝ) = 1 := by
    rw [mul_one] at h0
    linarith [h0]
  obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff (n : ℝ)).1 hcos
  have hkne : k ≠ 0 := by
    rintro rfl
    simp at hk
    exact absurd hk.symm (Nat.cast_ne_zero.mpr hn.ne')
  refine irrational_pi ⟨(n : ℚ) / (2 * (k : ℚ)), ?_⟩
  have hkR : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hkne
  push_cast
  field_simp
  linear_combination (-1 : ℝ) * hk

