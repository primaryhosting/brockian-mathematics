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

def timeB (C : Code) (k z : ℕ) : ℕ := (List.range (k + 1)).findIdx fun k' => (evaln k' C z).isSome

/-- The data the bounded construction depends on: a table of values of the speed-up factor,
the code being defined, and a fuel bound. -/
abbrev Env := (List ℕ × Code) × ℕ

/-- The speed-up factor, read off from the table. -/
