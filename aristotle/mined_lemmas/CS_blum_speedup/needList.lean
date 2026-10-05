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

def needList (n x : ℕ) : List ℕ :=
  ((List.range x).filter fun i => decide (n ≤ i)).flatMap fun i =>
    ((List.range (x + 1)).filter fun y => decide (i < y)).flatMap fun y =>
      (List.range (y + 1)).map fun e => Nat.pair (Nat.pair (i + 1) e) y

