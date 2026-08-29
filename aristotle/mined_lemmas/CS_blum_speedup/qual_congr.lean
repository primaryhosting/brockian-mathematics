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

theorem qual_congr {rf rf' T T' : ℕ → ℕ} {i y : ℕ}
    (hr : rf (maxCost T i y) = rf' (maxCost T' i y)) : qual rf T i y = qual rf' T' i y := by
  unfold qual
  rw [hr]

