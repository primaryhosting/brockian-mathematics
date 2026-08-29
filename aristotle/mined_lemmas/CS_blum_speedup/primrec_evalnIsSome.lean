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

theorem primrec_evalnIsSome : Primrec fun q : (Code × ℕ) × ℕ => (evaln q.1.2 q.1.1 q.2).isSome :=
  Primrec.option_isSome.comp (Nat.Partrec.Code.primrec_evaln.comp
    (Primrec.pair (Primrec.pair (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.fst))
      Primrec.snd))

