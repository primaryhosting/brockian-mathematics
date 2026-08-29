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

theorem log_le_harmonic (i : ℕ) : Real.log ((i : ℝ) + 1) ≤ ∑ k ∈ Finset.Ico 1 (i + 1), (1 / (k : ℝ)) := by
  induction i with
  | zero => simp
  | succ j ih =>
      rw [Finset.sum_Ico_succ_top (by omega)]
      have h1 : Real.log ((j : ℝ) + 1 + 1) - Real.log ((j : ℝ) + 1) ≤ 1 / ((j : ℝ) + 1) := by
        have h0 := Real.log_le_sub_one_of_pos (x := ((j : ℝ) + 1 + 1) / ((j : ℝ) + 1))
          (by positivity)
        rw [Real.log_div (by positivity) (by positivity)] at h0
        have h2 : ((j : ℝ) + 1 + 1) / ((j : ℝ) + 1) - 1 = 1 / ((j : ℝ) + 1) := by
          field_simp; ring
        linarith [h0, h2.le, h2.ge]
      push_cast
      push_cast at ih
      linarith

/-- Telescoping bound `∑_{k=1}^{N-1} 1/(k(k+1)) ≤ 1`. -/
