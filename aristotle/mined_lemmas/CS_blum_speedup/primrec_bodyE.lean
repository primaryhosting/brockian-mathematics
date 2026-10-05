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

theorem primrec_bodyE : Primrec fun p : Env × ℕ × ℕ => bodyE p.1 p.2.1 p.2.2 := by
  have htab : Primrec fun p : Env × ℕ × ℕ =>
      (Denumerable.ofNat (List (ℕ × ℕ)) p.2.1.unpair.2).lookup p.2.2 :=
    Primrec.listLookup.comp (Primrec.snd.comp Primrec.snd)
      ((Primrec.ofNat (List (ℕ × ℕ))).comp
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.snd))))
  have hels : Primrec fun p : Env × ℕ × ℕ =>
      leastNotIn (vals (rfE p.1) (costE p.1) p.2.1.unpair.1 p.2.2) :=
    primrec_leastNotIn.comp (primrec_vals.comp (Primrec.pair Primrec.fst
      (Primrec.pair (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.snd)))
        (Primrec.snd.comp Primrec.snd))))
  exact Primrec.option_getD.comp htab hels

/-- All sub-computations that the member `n` of the family needs at stage `x` have finished
within fuel `k`. -/
