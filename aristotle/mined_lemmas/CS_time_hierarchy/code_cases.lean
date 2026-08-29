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

theorem code_cases (c : ℕ) :
    c ≤ 6 ∨ ∃ i j, c = cPair i j ∨ c = cComp i j ∨ c = cPrec i j ∨ c = cRfind i j := by
  by_cases h : c ≤ 6
  · exact Or.inl h
  · right
    refine ⟨(Nat.unpair ((c - 7) / 4)).1, (Nat.unpair ((c - 7) / 4)).2, ?_⟩
    have hp : Nat.pair (Nat.unpair ((c - 7) / 4)).1 (Nat.unpair ((c - 7) / 4)).2 = (c - 7) / 4 :=
      Nat.pair_unpair _
    simp only [cPair, cComp, cPrec, cRfind, hp]
    omega

/-! ### Monotonicity in the step budget -/

