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

theorem canc_iff {rf T : ℕ → ℕ} {i x : ℕ} :
    canc rf T i x = true ↔
      i < x ∧ qual rf T i x = true ∧ ∀ y, i < y → y < x → qual rf T i y = false := by
  simp only [canc, Bool.and_eq_true, decide_eq_true_eq, allB_iff, Bool.or_eq_true,
    Bool.not_eq_true']
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, h2, fun y hy hyx => ?_⟩
    rcases h3 y hyx with h | h
    · omega
    · exact h
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, fun y hyx => if h : y ≤ i then Or.inl h else Or.inr (h3 y (by omega) hyx)⟩

/-- The list of values that must be avoided at stage `x` by the member `n` of the family. -/
