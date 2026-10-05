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

theorem halts_curry {c : Code} {m x : ℕ} (h : Halts c (Nat.pair m x)) : Halts (curry c m) x := by
  obtain ⟨k, hk⟩ := h
  rcases Option.isSome_iff_exists.1 hk with ⟨v, hv⟩
  exact ⟨k, Option.isSome_iff_exists.2 ⟨v, evaln_curry hv⟩⟩

