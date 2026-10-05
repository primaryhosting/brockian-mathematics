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

def vals (rf T : ℕ → ℕ) (n x : ℕ) : List ℕ :=
  (List.range x).filterMap fun i =>
    bif decide (n ≤ i) && canc rf T i x then
      some ((evaln (rf (maxCost T i x)) (Denumerable.ofNat Code i) x).getD 0)
    else none

