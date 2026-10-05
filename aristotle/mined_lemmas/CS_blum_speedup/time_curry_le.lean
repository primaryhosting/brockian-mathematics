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

theorem time_curry_le {c : Code} {m x : ℕ} (h : Halts c (Nat.pair m x)) :
    time (curry c m) x ≤ time c (Nat.pair m x) := by
  rcases Option.isSome_iff_exists.1 (time_isSome h) with ⟨v, hv⟩
  exact time_le (Option.isSome_iff_exists.2 ⟨v, evaln_curry hv⟩)

end CS

import RequestProject.BlumPrimrec

/-!
# The self-referential family of programs

Using Kleene's recursion theorem we build a single code `C` such that, for all `n`, `d` and `x`,

`eval C ⟪⟪n, d⟫, x⟫ = body r (time C) ⟪n, d⟫ x`,

i.e. the code computes the diagonal construction of `RequestProject.BlumCore` in which the
thresholds are given in terms of the running times of the code itself.
-/

set_option maxHeartbeats 1000000

namespace CS

open Nat.Partrec Nat.Partrec.Code

/-- The table of values of `r` on `0, …, k`. -/
