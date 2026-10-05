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

theorem evaln_const : ∀ (m : ℕ) {k x : ℕ}, x < k → m < k → evaln k (Code.const m) x = some m
  | 0, k + 1, x, hx, _ => by
      simp [Code.const, evaln, Nat.lt_succ_iff.1 hx]
  | m + 1, k + 1, x, hx, hm => by
      have ih := evaln_const m (k := k + 1) hx (by omega)
      simp [Code.const, evaln, ih, Nat.lt_succ_iff.1 hx, Nat.lt_succ_iff.1 (by omega : m < k + 1)]

