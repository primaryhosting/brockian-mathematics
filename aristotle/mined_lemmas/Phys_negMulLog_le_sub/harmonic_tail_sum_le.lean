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

theorem harmonic_tail_sum_le (N : ℕ) :
    ∑ k ∈ Finset.Ico 1 N, (1 / (k : ℝ)) * (1 / ((k : ℝ) + 1)) ≤ 1 := by
  have key : ∀ M : ℕ, ∑ k ∈ Finset.Ico 1 M, (1 / (k : ℝ)) * (1 / ((k : ℝ) + 1))
      ≤ 1 - 1 / (max M 1 : ℕ) := by
    intro M
    induction M with
    | zero => simp
    | succ j ih =>
        rcases Nat.eq_zero_or_pos j with hj | hj
        · subst hj; simp
        · rw [Finset.sum_Ico_succ_top (by omega)]
          have hjr : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
          have hm : ((max j 1 : ℕ) : ℝ) = (j : ℝ) := by rw [Nat.max_eq_left hj]
          rw [hm] at ih
          have hm2 : ((max (j + 1) 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by
            rw [Nat.max_eq_left (by omega)]; push_cast; ring
          rw [hm2]
          have hsplit : (1 / (j : ℝ)) * (1 / ((j : ℝ) + 1)) = 1 / (j : ℝ) - 1 / ((j : ℝ) + 1) := by
            field_simp; ring
          rw [hsplit]
          linarith
  refine (key N).trans ?_
  have h1 : (1 : ℝ) ≤ ((max N 1 : ℕ) : ℝ) := by exact_mod_cast le_max_right N 1
  have h2 : 0 < 1 / ((max N 1 : ℕ) : ℝ) := by positivity
  linarith

/-- Partial sums of `∑ 1/(i+1)^2` are bounded by `2`. -/
