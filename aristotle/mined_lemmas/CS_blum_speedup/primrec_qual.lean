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

theorem primrec_qual :
    Primrec fun p : Env × ℕ × ℕ => qual (rfE p.1) (costE p.1) p.2.1 p.2.2 := by
  refine Primrec.option_isSome.comp (Nat.Partrec.Code.primrec_evaln.comp
    (Primrec.pair (Primrec.pair
      (f := fun p : Env × ℕ × ℕ => rfE p.1 (maxCost (costE p.1) p.2.1 p.2.2))
      (g := fun p : Env × ℕ × ℕ => Denumerable.ofNat Code p.2.1) ?_ ?_)
      (Primrec.snd.comp Primrec.snd)))
  · exact primrec_rfE.comp Primrec.fst primrec_maxCost
  · exact (Primrec.ofNat Code).comp (Primrec.fst.comp Primrec.snd)

