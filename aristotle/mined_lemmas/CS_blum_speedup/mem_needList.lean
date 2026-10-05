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

theorem mem_needList {n x i y e : ℕ} (hni : n ≤ i) (hix : i < x) (hiy : i < y) (hyx : y ≤ x)
    (hey : e ≤ y) : Nat.pair (Nat.pair (i + 1) e) y ∈ needList n x := by
  simp only [needList, List.mem_flatMap, List.mem_filter, List.mem_range, List.mem_map,
    decide_eq_true_eq]
  exact ⟨i, ⟨hix, hni⟩, y, ⟨Nat.lt_succ_of_le hyx, hiy⟩, e, Nat.lt_succ_of_le hey, rfl⟩

