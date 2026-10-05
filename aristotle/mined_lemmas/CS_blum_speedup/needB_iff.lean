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

theorem needB_iff {C : Code} {k n x : ℕ} :
    needB C k n x = true ↔
      ∀ i, n ≤ i → i < x → ∀ y, i < y → y ≤ x → ∀ d, d ≤ y →
        (evaln k C (Nat.pair (Nat.pair (i + 1) d) y)).isSome = true := by
  simp only [needB, allB_iff, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · intro h i hni hix y hiy hyx d hdy
    rcases h i hix with h | h
    · omega
    · rcases h y (by omega) with h | h
      · omega
      · exact h d (by omega)
  · intro h i hix
    by_cases hni : i < n
    · exact Or.inl hni
    refine Or.inr fun y hyx => ?_
    by_cases hiy : y ≤ i
    · exact Or.inl hiy
    exact Or.inr fun d hdy => h i (by omega) hix y (by omega) (by omega) d (by omega)

