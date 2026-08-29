/-
# Time Hierarchy
Category: Frontier Cs
Target: CS.time_hierarchy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

/-! ## A clocked model of computation

Programs are natural numbers (their own Gödel numbers).  A code `c` is decoded
on the fly:

* `0` : the constant `0`
* `1` : the successor function
* `2` : first projection of the Cantor pairing
* `3` : second projection of the Cantor pairing
* `4` : the *clocked universal machine*: on input `⟪c', y, k⟫` it simulates the
  program `c'` on input `y` for `k` steps and outputs the result (or `0` if
  the simulation did not finish);  this costs `k + 1` steps
* `5` : the boolean complement `x ↦ if x = 0 then 1 else 0`
* `6` : the identity
* `7 + 4 * ⟪i, j⟫ + 0` : pairing of the results of `i` and `j`
* `7 + 4 * ⟪i, j⟫ + 1` : composition `i ∘ j`
* `7 + 4 * ⟪i, j⟫ + 2` : primitive recursion
* `7 + 4 * ⟪i, j⟫ + 3` : unbounded search (`rfind`)

`eval s c x` runs the program `c` on input `x` with a budget of `s` steps and
returns `none` if the budget is exhausted.  Every constructor consumes one unit
of the budget, so `eval` is a genuine (if coarse) cost model. -/

theorem diag_not_mem_TIME (t : ℕ → ℕ) : diag t ∉ TIME t := by
  rintro ⟨c, hc⟩
  have h := hc c
  have hv : (eval (t c) c c).getD 0 = if diag t c then 1 else 0 := by rw [h]; rfl
  have hd : diag t c = true ↔ (eval (t c) c c).getD 0 = 0 := by simp [diag]
  by_cases hb : diag t c = true
  · have h0 : (eval (t c) c c).getD 0 = 0 := hd.mp hb
    rw [hb] at hv
    simp only [if_true] at hv
    omega
  · have h0 : (eval (t c) c c).getD 0 ≠ 0 := fun hz => hb (hd.mpr hz)
    simp only [Bool.not_eq_true] at hb
    rw [hb] at hv
    simp only [Bool.false_eq_true, if_false] at hv
    exact h0 hv

/-- The code of the diagonalizing program: given a program `ct` that maps `x` to the
triple `⟪x, x, t x⟫`, first build that triple, then run the clocked universal
machine on it, then complement the answer. -/
