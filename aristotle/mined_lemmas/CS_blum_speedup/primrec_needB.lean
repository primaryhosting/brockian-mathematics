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

theorem primrec_needB : Primrec fun p : Code × ℕ × ℕ × ℕ => needB p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  have h3 : Primrec fun q : (Code × ℕ × ℕ × ℕ) × ℕ × ℕ =>
      allB (q.2.2 + 1)
        (fun d => (evaln q.1.2.1 q.1.1 (Nat.pair (Nat.pair (q.2.1 + 1) d) q.2.2)).isSome) := by
    refine primrec_allB (m := fun q : (Code × ℕ × ℕ × ℕ) × ℕ × ℕ => q.2.2 + 1)
      (f := fun (q : (Code × ℕ × ℕ × ℕ) × ℕ × ℕ) (d : ℕ) =>
        (evaln q.1.2.1 q.1.1 (Nat.pair (Nat.pair (q.2.1 + 1) d) q.2.2)).isSome)
      (Primrec.succ.comp (Primrec.snd.comp (Primrec.snd))) (Primrec₂.mk ?_)
    refine primrec_evalnIsSome.comp
      (g := fun a : ((Code × ℕ × ℕ × ℕ) × ℕ × ℕ) × ℕ =>
        ((a.1.1.1, a.1.1.2.1), Nat.pair (Nat.pair (a.1.2.1 + 1) a.2) a.1.2.2)) ?_
    refine Primrec.pair (Primrec.pair
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))) ?_
    exact Primrec₂.natPair.comp
      (Primrec₂.natPair.comp
        (Primrec.succ.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))) Primrec.snd)
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have h2 : Primrec fun q : (Code × ℕ × ℕ × ℕ) × ℕ =>
      allB (q.1.2.2.2 + 1) (fun y => decide (y ≤ q.2) ||
        allB (y + 1)
          (fun d => (evaln q.1.2.1 q.1.1 (Nat.pair (Nat.pair (q.2 + 1) d) y)).isSome)) := by
    refine primrec_allB (m := fun q : (Code × ℕ × ℕ × ℕ) × ℕ => q.1.2.2.2 + 1)
      (f := fun (q : (Code × ℕ × ℕ × ℕ) × ℕ) (y : ℕ) => decide (y ≤ q.2) ||
        allB (y + 1)
          (fun d => (evaln q.1.2.1 q.1.1 (Nat.pair (Nat.pair (q.2 + 1) d) y)).isSome))
      (Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
      (Primrec₂.mk ?_)
    refine Primrec.or.comp
      (primrec_decide (Primrec.nat_le.comp Primrec.snd (Primrec.snd.comp Primrec.fst))) ?_
    refine h3.comp (g := fun a : ((Code × ℕ × ℕ × ℕ) × ℕ) × ℕ => (a.1.1, (a.1.2, a.2))) ?_
    exact Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)
  refine primrec_allB (m := fun p : Code × ℕ × ℕ × ℕ => p.2.2.2)
    (f := fun (p : Code × ℕ × ℕ × ℕ) (i : ℕ) => decide (i < p.2.2.1) ||
      allB (p.2.2.2 + 1) (fun y => decide (y ≤ i) ||
        allB (y + 1) (fun d => (evaln p.2.1 p.1 (Nat.pair (Nat.pair (i + 1) d) y)).isSome)))
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)) (Primrec₂.mk ?_)
  refine Primrec.or.comp
    (primrec_decide (Primrec.nat_lt.comp Primrec.snd
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))) ?_
  refine h2.comp (g := fun a : (Code × ℕ × ℕ × ℕ) × ℕ => (a.1, a.2)) ?_
  exact Primrec.pair Primrec.fst Primrec.snd

end CS

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

