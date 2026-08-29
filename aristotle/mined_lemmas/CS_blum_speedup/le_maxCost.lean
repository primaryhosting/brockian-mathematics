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

theorem le_maxCost (T : ℕ → ℕ) {i y d : ℕ} (hd : d ≤ y) :
    T (Nat.pair (Nat.pair (i + 1) d) y) ≤ maxCost T i y :=
  le_foldr_max (List.mem_map.2 ⟨d, List.mem_range.2 (Nat.lt_succ_of_le hd), rfl⟩)

