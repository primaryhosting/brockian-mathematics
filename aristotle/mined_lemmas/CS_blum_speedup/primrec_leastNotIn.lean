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

theorem primrec_leastNotIn : Primrec leastNotIn :=
  Primrec.list_findIdx (f := fun V : List ℕ => List.range (V.length + 1))
    (p := fun V v => !V.contains v)
    (Primrec.list_range.comp (Primrec.succ.comp Primrec.list_length))
    (Primrec₂.mk (Primrec.not.comp (primrec_contains.comp Primrec.fst Primrec.snd)))

