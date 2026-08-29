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

theorem eval_cTriple (N x : ℕ) :
    eval (N + 3) (cTriple N) x = some (Nat.pair x (Nat.pair x N)) := by
  have h1 : eval (N + 2) (cPair cId (cConst N)) x = some (Nat.pair x N) := by
    rw [show N + 2 = (N+1) + 1 from rfl, eval_cPair, eval_cConst N x]
    simp
  rw [cTriple, show N + 3 = (N+2) + 1 from rfl, eval_cPair, h1]
  simp

/-- **Time hierarchy theorem, constant bounds.**  Strictly more languages can be
decided in `2 * N + 6` steps than in `N` steps. -/
