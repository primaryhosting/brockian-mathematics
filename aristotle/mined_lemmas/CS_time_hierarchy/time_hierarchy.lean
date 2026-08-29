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

theorem time_hierarchy (t T τ : ℕ → ℕ) (ct : ℕ)
    (hct : ∀ x, eval (τ x) ct x = some (Nat.pair x (Nat.pair x (t x))))
    (hT : ∀ x, τ x + t x + 3 ≤ T x) :
    TIME t ⊂ TIME T := by
  have hsub : TIME t ⊆ TIME T := TIME_mono (fun x => by have := hT x; omega)
  rw [Set.ssubset_iff_of_subset hsub]
  refine ⟨diag t, ⟨cDiag ct, fun x => ?_⟩, diag_not_mem_TIME t⟩
  exact eval_mono (hT x) (eval_cDiag t τ ct hct x)

/-! ## The hypotheses are satisfiable: constant time bounds

To see that the hierarchy theorem is not vacuous we exhibit, for every constant
time bound, a program computing the required triple `⟪x, x, t x⟫`. -/

/-- A program computing the constant `n`. -/
