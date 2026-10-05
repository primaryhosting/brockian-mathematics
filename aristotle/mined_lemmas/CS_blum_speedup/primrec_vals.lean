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

theorem primrec_vals :
    Primrec fun p : Env × ℕ × ℕ => vals (rfE p.1) (costE p.1) p.2.1 p.2.2 := by
  refine Primrec.listFilterMap
    (f := fun p : Env × ℕ × ℕ => List.range p.2.2)
    (g := fun (p : Env × ℕ × ℕ) (i : ℕ) =>
      bif decide (p.2.1 ≤ i) && canc (rfE p.1) (costE p.1) i p.2.2 then
        some ((evaln (rfE p.1 (maxCost (costE p.1) i p.2.2))
          (Denumerable.ofNat Code i) p.2.2).getD 0)
      else none)
    (Primrec.list_range.comp (Primrec.snd.comp Primrec.snd)) (Primrec₂.mk ?_)
  have hcanc : Primrec fun q : (Env × ℕ × ℕ) × ℕ =>
      canc (rfE q.1.1) (costE q.1.1) q.2 q.1.2.2 :=
    primrec_canc.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.pair Primrec.snd (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
  have hcond : Primrec fun q : (Env × ℕ × ℕ) × ℕ =>
      (decide (q.1.2.1 ≤ q.2) && canc (rfE q.1.1) (costE q.1.1) q.2 q.1.2.2) :=
    Primrec.and.comp
      (primrec_decide
        (Primrec.nat_le.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd))
      hcanc
  have hmax : Primrec fun q : (Env × ℕ × ℕ) × ℕ => maxCost (costE q.1.1) q.2 q.1.2.2 :=
    primrec_maxCost.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.pair Primrec.snd (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
  have hval : Primrec fun q : (Env × ℕ × ℕ) × ℕ =>
      (evaln (rfE q.1.1 (maxCost (costE q.1.1) q.2 q.1.2.2))
        (Denumerable.ofNat Code q.2) q.1.2.2).getD 0 := by
    refine Primrec.option_getD.comp (Nat.Partrec.Code.primrec_evaln.comp
      (Primrec.pair (Primrec.pair
        (f := fun q : (Env × ℕ × ℕ) × ℕ => rfE q.1.1 (maxCost (costE q.1.1) q.2 q.1.2.2))
        (g := fun q : (Env × ℕ × ℕ) × ℕ => Denumerable.ofNat Code q.2) ?_ ?_)
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))) (Primrec.const 0)
    · exact primrec_rfE.comp (Primrec.fst.comp Primrec.fst) hmax
    · exact (Primrec.ofNat Code).comp Primrec.snd
  exact Primrec.cond hcond (Primrec.option_some.comp hval) (Primrec.const none)

