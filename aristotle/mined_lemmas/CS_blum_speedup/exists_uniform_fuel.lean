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

theorem exists_uniform_fuel {C : Code} (L : List ℕ) (h : ∀ z ∈ L, Halts C z) :
    ∃ k, ∀ z ∈ L, (evaln k C z).isSome := by
  induction L with
  | nil => exact ⟨0, by simp⟩
  | cons z L ih =>
    obtain ⟨k, hk⟩ := ih fun w hw => h w (List.mem_cons_of_mem _ hw)
    obtain ⟨k', hk'⟩ := h z List.mem_cons_self
    refine ⟨max k k', fun w hw => ?_⟩
    rcases List.mem_cons.1 hw with rfl | hw
    · exact isSome_of_time_le ⟨k', hk'⟩ (le_trans (time_le hk') (le_max_right _ _))
    · exact isSome_of_time_le ⟨k, hk w hw⟩ (le_trans (time_le (hk w hw)) (le_max_left _ _))

/-- The list of inputs consulted by the member `n` of the family at stage `x`. -/
