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

theorem isSome_of_time_le {c : Code} {x k : ℕ} (h : Halts c x) (hk : time c x ≤ k) :
    (evaln k c x).isSome := by
  rcases Option.isSome_iff_exists.1 (time_isSome h) with ⟨v, hv⟩
  exact Option.isSome_iff_exists.2 ⟨v, evaln_mono hk hv⟩

