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

theorem mem_vals {rf T : ℕ → ℕ} {n x v : ℕ} :
    v ∈ vals rf T n x ↔ ∃ i < x, n ≤ i ∧ canc rf T i x = true ∧
      v = (evaln (rf (maxCost T i x)) (Denumerable.ofNat Code i) x).getD 0 := by
  simp only [vals, List.mem_filterMap, List.mem_range, Bool.cond_eq_ite]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hc : (decide (n ≤ i) && canc rf T i x) = true
    · rw [if_pos hc] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact ⟨i, hi, hc.1, hc.2, (Option.some_inj.1 h).symm⟩
    · rw [if_neg hc] at h; exact absurd h (by simp)
  · rintro ⟨i, hi, hni, hc, rfl⟩
    refine ⟨i, hi, ?_⟩
    rw [if_pos (by simp [hni, hc])]

/-- The value produced at stage `x` by the member `z = (n, d)` of the family: the entry of the
finite table `d` at `x` if there is one, and otherwise the least value avoiding `vals`. -/
