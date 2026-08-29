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

theorem partrec_Psi {r : ℕ → ℕ} (hr : Computable r) : Partrec₂ (Psi r) := by
  have hneed : Partrec₂ fun (p : Code × ℕ) (k : ℕ) =>
      (Part.some (needB p.1 k p.2.unpair.1.unpair.1 p.2.unpair.2) : Part Bool) := by
    refine Computable₂.partrec₂ (Computable₂.mk ?_)
    refine (primrec_needB.to_comp).comp
      (g := fun a : (Code × ℕ) × ℕ =>
        (a.1.1, (a.2, (a.1.2.unpair.1.unpair.1, a.1.2.unpair.2)))) ?_
    exact Computable.pair (Computable.fst.comp Computable.fst)
      (Computable.pair Computable.snd
        (Computable.pair
          (Computable.fst.comp (Computable.unpair.comp (Computable.fst.comp
            (Computable.unpair.comp (Computable.snd.comp Computable.fst)))))
          (Computable.snd.comp (Computable.unpair.comp (Computable.snd.comp Computable.fst)))))
  have hbody : Computable₂ fun (p : Code × ℕ) (k : ℕ) =>
      bodyE ((rtab r k, p.1), k) p.2.unpair.1 p.2.unpair.2 := by
    refine Computable₂.mk ((primrec_bodyE.to_comp).comp
      (g := fun a : (Code × ℕ) × ℕ =>
        (((rtab r a.2, a.1.1), a.2), (a.1.2.unpair.1, a.1.2.unpair.2))) ?_)
    refine Computable.pair (Computable.pair
      (Computable.pair ((computable_rtab hr).comp Computable.snd)
        (Computable.fst.comp Computable.fst)) Computable.snd) ?_
    exact Computable.pair
      (Computable.fst.comp (Computable.unpair.comp (Computable.snd.comp Computable.fst)))
      (Computable.snd.comp (Computable.unpair.comp (Computable.snd.comp Computable.fst)))
  exact Partrec.map (Partrec.rfind hneed) hbody

