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

theorem eval_cRfind (s i j x : ℕ) :
    eval (s+1) (cRfind i j) x =
      (eval s i x).bind fun v =>
        if v = 0 then some (Nat.unpair x).2
        else eval s (cRfind i j) (Nat.pair (Nat.unpair x).1 ((Nat.unpair x).2 + 1)) := by
  have hu : Nat.unpair (Nat.pair i j) = (i, j) := Nat.unpair_pair i j
  simp only [cRfind]
  generalize Nat.pair i j = p at hu ⊢
  rw [eval]
  simp only [hu, show (7 + 4*p + 3 - 7) % 4 = 3 from by omega,
    show (7 + 4*p + 3 - 7) / 4 = p from by omega,
    show ¬ (7+4*p+3 = 0) from by omega, show ¬ (7+4*p+3 = 1) from by omega,
    show ¬ (7+4*p+3 = 2) from by omega, show ¬ (7+4*p+3 = 3) from by omega,
    show ¬ (7+4*p+3 = 4) from by omega, show ¬ (7+4*p+3 = 5) from by omega,
    show ¬ (7+4*p+3 = 6) from by omega, OfNat.ofNat_ne_zero, if_false,
    show (3:ℕ) ≠ 1 from by omega, show (3:ℕ) ≠ 2 from by omega]

/-- Every code is one of the seven atomic codes or a compound code. -/
