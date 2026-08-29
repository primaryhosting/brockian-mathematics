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

theorem allB_congr {m : ℕ} {p q : ℕ → Bool} (h : ∀ i < m, p i = q i) : allB m p = allB m q := by
  have key : ∀ l : List ℕ, (∀ i ∈ l, p i = q i) → l.all p = l.all q := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih => intro h; simp_all
  exact key _ fun i hi => h i (List.mem_range.1 hi)

