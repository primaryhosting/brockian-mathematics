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

theorem sum_inv_sq_le (N : ℕ) :
    ∑ i ∈ Finset.range N, (1 / ((i : ℝ) + 1) ^ 2) ≤ 2 - 1 / ((max N 1 : ℕ) : ℝ) := by
  induction N with
  | zero => norm_num
  | succ j ih =>
      rcases Nat.eq_zero_or_pos j with hj | hj
      · subst hj; norm_num
      · rw [Finset.sum_range_succ]
        have hjr : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
        have hm : ((max j 1 : ℕ) : ℝ) = (j : ℝ) := by rw [Nat.max_eq_left hj]
        rw [hm] at ih
        have hm2 : ((max (j + 1) 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by
          rw [Nat.max_eq_left (by omega)]; push_cast; ring
        rw [hm2]
        have hkey : 1 / ((j : ℝ) + 1) ^ 2 ≤ 1 / (j : ℝ) - 1 / ((j : ℝ) + 1) := by
          have h1 : 1 / (j : ℝ) - 1 / ((j : ℝ) + 1) = 1 / ((j : ℝ) * ((j : ℝ) + 1)) := by
            field_simp; ring
          rw [h1]
          apply one_div_le_one_div_of_le
          · positivity
          · nlinarith
        linarith

/-- The logarithmic mean is bounded when the tails decay like `C/(k+1)`. -/
