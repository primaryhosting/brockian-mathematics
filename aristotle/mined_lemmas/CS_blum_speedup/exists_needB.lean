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

theorem exists_needB {C : Code} {n x : ℕ}
    (h : ∀ i, n ≤ i → i < x → ∀ y, i < y → y ≤ x → ∀ e ≤ y,
      Halts C (Nat.pair (Nat.pair (i + 1) e) y)) : ∃ k, needB C k n x = true := by
  have hL : ∀ z ∈ needList n x, Halts C z := by
    intro z hz
    simp only [needList, List.mem_flatMap, List.mem_filter, List.mem_range, List.mem_map,
      decide_eq_true_eq] at hz
    obtain ⟨i, ⟨hix, hni⟩, y, ⟨hy, hiy⟩, e, he, rfl⟩ := hz
    exact h i hni hix y hiy (Nat.lt_succ_iff.1 hy) e (Nat.lt_succ_iff.1 he)
  obtain ⟨k, hk⟩ := exists_uniform_fuel _ hL
  exact ⟨k, needB_iff.2 fun i hni hix y hiy hyx e hey =>
    hk _ (mem_needList hni hix hiy hyx hey)⟩

end CS

import RequestProject.BlumCore

/-!
# Primitive recursiveness of the bounded construction

Here we check that the construction of `RequestProject.BlumCore`, instantiated with a
*bounded* time oracle (`timeB`) and a finite table of values of the speed-up factor,
is primitive recursive in all of its arguments.
-/

set_option maxHeartbeats 1000000

namespace CS

open Primrec Nat.Partrec Nat.Partrec.Code

/-- Bounded running time: the least `k' ≤ k` for which `evaln k' C z` succeeds
(and `k+1` if there is none). -/
