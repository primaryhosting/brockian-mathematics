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

theorem primrec_timeB : Primrec fun p : Code × ℕ × ℕ => timeB p.1 p.2.1 p.2.2 := by
  refine Primrec.list_findIdx (f := fun p : Code × ℕ × ℕ => List.range (p.2.1 + 1))
    (p := fun p k' => (evaln k' p.1 p.2.2).isSome)
    (Primrec.list_range.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))) ?_
  refine Primrec₂.mk (Primrec.option_isSome.comp ?_)
  exact Nat.Partrec.Code.primrec_evaln.comp
    (Primrec.pair (Primrec.pair Primrec.snd (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))

