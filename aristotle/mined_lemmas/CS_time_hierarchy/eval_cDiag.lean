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

theorem eval_cDiag (t τ : ℕ → ℕ) (ct : ℕ)
    (hct : ∀ x, eval (τ x) ct x = some (Nat.pair x (Nat.pair x (t x)))) (x : ℕ) :
    eval (τ x + t x + 3) (cDiag ct) x = some (if diag t x then 1 else 0) := by
  have hsim : eval (τ x + t x + 2) (cComp cUniv ct) x = some ((eval (t x) x x).getD 0) := by
    rw [show τ x + t x + 2 = (τ x + t x + 1) + 1 from rfl, eval_cComp]
    rw [eval_mono (show τ x ≤ τ x + t x + 1 by omega) (hct x)]
    simpa using eval_cUniv (τ x + t x) x x (t x) (by omega)
  rw [cDiag, show τ x + t x + 3 = (τ x + t x + 2) + 1 from rfl, eval_cComp, hsim]
  simp only [Option.bind_some, eval_cNot, diag]
  by_cases hz : (eval (t x) x x).getD 0 = 0 <;> simp [hz]

/-- **Time hierarchy theorem.**  Let `t` be a time bound such that the map
`x ↦ ⟪x, x, t x⟫` is computable by the program `ct` within `τ x` steps (a
time-constructibility hypothesis), and let `T` be any time bound exceeding
`τ + t + 3`.  Then strictly more languages are decidable in time `T` than in
time `t`: the diagonal language `diag t` witnesses the strict inclusion. -/
