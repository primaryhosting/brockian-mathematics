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

theorem vals_congr {rf rf' T T' : ℕ → ℕ} {n x : ℕ} (h : Agree rf rf' T T' n x) :
    vals rf T n x = vals rf' T' n x := by
  unfold vals
  refine List.filterMap_congr ?_
  intro i hi
  have hix : i < x := List.mem_range.1 hi
  by_cases hni : n ≤ i
  · obtain ⟨-, hr⟩ := h i hni hix x hix le_rfl
    rw [canc_congr h hni hix, hr]
  · simp [decide_eq_false (by omega : ¬ n ≤ i)]

