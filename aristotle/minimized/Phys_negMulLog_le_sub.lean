import Mathlib
/-!
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires `import` to be the very first command of a module, so the
requested header block appears immediately after the single `import Mathlib` line.
-/

open scoped BigOperators ComplexOrder
open Matrix

namespace Phys

/-! ## Elementary entropy inequalities -/

/-- Gibbs-type pointwise bound: for `x ≥ 0` and a reference weight `r > 0`,
`-x log x ≤ (r - x) - x log r`. -/

theorem negMulLog_le_sub (x r : ℝ) (hx : 0 ≤ x) (hr : 0 < r) :
    Real.negMulLog x ≤ (r - x) + x * (-Real.log r) := by
  rcases eq_or_lt_of_le hx with h | h
  · simp [Real.negMulLog, ← h]; linarith
  · have h1 : Real.log (r / x) ≤ r / x - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h2 : Real.log (r / x) = Real.log r - Real.log x :=
      Real.log_div (ne_of_gt hr) (ne_of_gt h)
    have h3 := mul_le_mul_of_nonneg_left h1 hx
    rw [h2] at h3
    have hxx : x * (r / x - 1) = r - x := by field_simp
    rw [hxx] at h3
    simp only [Real.negMulLog]
    nlinarith

/-- **Gibbs' inequality.**  The Shannon entropy of a probability vector `p` is bounded by its
cross-entropy against any positive sub-probability reference vector `r`. -/
