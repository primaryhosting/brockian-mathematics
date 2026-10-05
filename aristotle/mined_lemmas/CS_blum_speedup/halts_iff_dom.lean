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

theorem halts_iff_dom {c : Code} {x : ℕ} : Halts c x ↔ (eval c x).Dom := by
  constructor
  · rintro ⟨k, hk⟩
    rcases Option.isSome_iff_exists.1 hk with ⟨v, hv⟩
    exact (evaln_sound hv).fst
  · intro h
    obtain ⟨k, hk⟩ := evaln_complete.1 (Part.get_mem h)
    exact ⟨k, Option.isSome_iff_exists.2 ⟨_, hk⟩⟩

