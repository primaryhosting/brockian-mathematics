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

theorem not_isSome_iff_lt_time {c : Code} {x k : ℕ} (h : Halts c x) :
    ¬ (evaln k c x).isSome ↔ k < time c x := by
  constructor
  · intro hk
    by_contra hle
    exact hk (isSome_of_time_le h (not_lt.1 hle))
  · intro hk hs
    exact absurd (time_le hs) (not_le.2 hk)

