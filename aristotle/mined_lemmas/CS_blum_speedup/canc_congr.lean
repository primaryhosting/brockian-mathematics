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

theorem canc_congr {rf rf' T T' : ℕ → ℕ} {n i x : ℕ} (h : Agree rf rf' T T' n x)
    (hni : n ≤ i) (hix : i < x) : canc rf T i x = canc rf' T' i x := by
  have hqual : ∀ y, i < y → y ≤ x → qual rf T i y = qual rf' T' i y := by
    intro y hiy hyx
    obtain ⟨-, hr⟩ := h i hni hix y hiy hyx
    exact qual_congr hr
  unfold canc
  rw [hqual x hix le_rfl]
  congr 1
  refine allB_congr ?_
  intro y hy
  rcases lt_or_ge i y with hiy | hiy
  · rw [hqual y hiy (le_of_lt hy)]
  · simp [decide_eq_true (by omega : y ≤ i)]

