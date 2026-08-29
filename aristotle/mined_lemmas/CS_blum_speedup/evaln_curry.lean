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

theorem evaln_curry {c : Code} {m x k v : ℕ} (h : evaln k c (Nat.pair m x) = some v) :
    evaln k (curry c m) x = some v := by
  have hb : Nat.pair m x < k := evaln_bound h
  have hx : x < k := lt_of_le_of_lt (Nat.right_le_pair m x) hb
  have hm : m < k := lt_of_le_of_lt (Nat.left_le_pair m x) hb
  cases k with
  | zero => omega
  | succ k =>
    simp [curry, evaln, Nat.lt_succ_iff.1 hx, Seq.seq, evaln_const m hx hm, evaln_id hx, h]

