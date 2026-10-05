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

theorem maxCost_congr {T T' : ℕ → ℕ} {i y : ℕ}
    (h : ∀ d ≤ y, T (Nat.pair (Nat.pair (i + 1) d) y) = T' (Nat.pair (Nat.pair (i + 1) d) y)) :
    maxCost T i y = maxCost T' i y := by
  unfold maxCost
  congr 1
  refine List.map_congr_left ?_
  intro d hd
  exact h d (Nat.lt_succ_iff.1 (List.mem_range.1 hd))

/-- Index `i` *qualifies* at stage `y` if the code with index `i` halts on `y` within the
threshold `rf (maxCost T i y)`. -/
