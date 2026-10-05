import RequestProject.BlumTime

/-!
# The core of the speed-up construction

This file contains the (first-order, oracle-parametrised) combinatorial core of the
diagonal construction used in the proof of Blum's speed-up theorem.

The construction is parametrised by two functions:

* `rf : ℕ → ℕ`, the speed-up factor;
* `T : ℕ → ℕ`, an oracle giving the running time of the (self-referential) code under
  construction at a given input.
-/

namespace CS

open Nat.Partrec Nat.Partrec.Code

/-! ### Small helpers -/

/-- Bounded universal quantifier, as a `Bool`. -/

theorem evaln_id {k x : ℕ} (hx : x < k) : evaln k Code.id x = some x := by
  cases k with
  | zero => omega
  | succ k => simp [Code.id, evaln, Nat.lt_succ_iff.1 hx, Seq.seq]

/-- Currying costs nothing in this measure: any fuel that suffices for `c` on the pair
`(m, x)` also suffices for `curry c m` on `x`. -/
