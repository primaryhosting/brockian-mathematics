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

theorem maxCost_le {T : ℕ → ℕ} {i y k : ℕ}
    (h : ∀ e ≤ y, T (Nat.pair (Nat.pair (i + 1) e) y) ≤ k) : maxCost T i y ≤ k := by
  refine foldr_max_le ?_
  intro a ha
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha
  exact h e (Nat.lt_succ_iff.1 (List.mem_range.1 he))

