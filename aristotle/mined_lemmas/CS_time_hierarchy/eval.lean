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

def eval : ℕ → ℕ → ℕ → Option ℕ
  | 0, _, _ => none
  | s+1, c, x =>
    if c = 0 then some 0
    else if c = 1 then some (x + 1)
    else if c = 2 then some (Nat.unpair x).1
    else if c = 3 then some (Nat.unpair x).2
    else if c = 4 then
      (if _h : (Nat.unpair (Nat.unpair x).2).2 ≤ s then
        some ((eval (Nat.unpair (Nat.unpair x).2).2 (Nat.unpair x).1
                (Nat.unpair (Nat.unpair x).2).1).getD 0)
      else none)
    else if c = 5 then some (if x = 0 then 1 else 0)
    else if c = 6 then some x
    else
      if (c - 7) % 4 = 0 then
        (eval s (Nat.unpair ((c - 7) / 4)).1 x).bind fun a =>
          (eval s (Nat.unpair ((c - 7) / 4)).2 x).map fun b => Nat.pair a b
      else if (c - 7) % 4 = 1 then
        (eval s (Nat.unpair ((c - 7) / 4)).2 x).bind fun b =>
          eval s (Nat.unpair ((c - 7) / 4)).1 b
      else if (c - 7) % 4 = 2 then
        (match (Nat.unpair x).2 with
         | 0 => eval s (Nat.unpair ((c - 7) / 4)).1 (Nat.unpair x).1
         | n+1 => (eval s c (Nat.pair (Nat.unpair x).1 n)).bind fun v =>
                    eval s (Nat.unpair ((c - 7) / 4)).2 (Nat.pair (Nat.unpair x).1 (Nat.pair n v)))
      else
        (eval s (Nat.unpair ((c - 7) / 4)).1 x).bind fun v =>
          if v = 0 then some (Nat.unpair x).2
          else eval s c (Nat.pair (Nat.unpair x).1 ((Nat.unpair x).2 + 1))
termination_by s => s

/-- Code of the clocked universal machine. -/
