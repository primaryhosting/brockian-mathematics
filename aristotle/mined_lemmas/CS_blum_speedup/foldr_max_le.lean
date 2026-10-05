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

theorem foldr_max_le {k : ℕ} : ∀ {l : List ℕ}, (∀ a ∈ l, a ≤ k) → l.foldr max 0 ≤ k := by
  intro l
  induction l with
  | nil => simp
  | cons b l ih =>
    intro h
    simp only [List.foldr_cons, max_le_iff]
    exact ⟨h b List.mem_cons_self, ih fun a ha => h a (List.mem_cons_of_mem _ ha)⟩

