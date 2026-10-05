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

theorem timeB_eq_time {C : Code} {k z : ℕ} (h : (evaln k C z).isSome) : timeB C k z = time C z := by
  have hhalt : Halts C z := ⟨k, h⟩
  have hle : time C z ≤ k := time_le h
  have hlen : time C z < (List.range (k + 1)).length := by simp; omega
  refine List.findIdx_eq hlen |>.2 ⟨?_, ?_⟩
  · rw [List.getElem_range]
    exact time_isSome hhalt
  · intro j hj
    rw [List.getElem_range]
    have := (not_isSome_iff_lt_time (k := j) hhalt).2 hj
    simpa using this

