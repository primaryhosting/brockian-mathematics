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

theorem primrec_canc :
    Primrec fun p : Env × ℕ × ℕ => canc (rfE p.1) (costE p.1) p.2.1 p.2.2 := by
  have hq : Primrec₂ fun (p : Env × ℕ × ℕ) (y : ℕ) => qual (rfE p.1) (costE p.1) p.2.1 y :=
    Primrec₂.mk (primrec_qual.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)))
  have hall : Primrec fun p : Env × ℕ × ℕ =>
      allB p.2.2 (fun y => decide (y ≤ p.2.1) || !qual (rfE p.1) (costE p.1) p.2.1 y) := by
    refine primrec_allB (m := fun p : Env × ℕ × ℕ => p.2.2)
      (f := fun (p : Env × ℕ × ℕ) (y : ℕ) =>
        decide (y ≤ p.2.1) || !qual (rfE p.1) (costE p.1) p.2.1 y)
      (Primrec.snd.comp Primrec.snd) (Primrec₂.mk ?_)
    refine Primrec.or.comp ?_ (Primrec.not.comp (hq.comp Primrec.fst Primrec.snd))
    exact primrec_decide
      (Primrec.nat_le.comp Primrec.snd (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
  refine Primrec.and.comp (Primrec.and.comp ?_ primrec_qual) hall
  exact primrec_decide
    (Primrec.nat_lt.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))

