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

noncomputable def Psi (r : ℕ → ℕ) (C : Code) (w : ℕ) : Part ℕ :=
  (Nat.rfind fun k => Part.some (needB C k w.unpair.1.unpair.1 w.unpair.2)).map fun k =>
    bodyE ((rtab r k, C), k) w.unpair.1 w.unpair.2

