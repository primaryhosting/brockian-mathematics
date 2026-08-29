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

import RequestProject.Blum.Cost

/-!
# The Blum speedup construction

We build, by the recursion theorem, a code `blumCode` computing a two-parameter family of
functions `f i t` (`i` an index bound, `t` a patch threshold) with the following features.

At stage `x`, the function `f i 0` diagonalises against every program `j ≥ i` which is
*cheap at stage `x`*, meaning that `cost j x ≤ M j x + x` where `M j x` is the maximal cost of
the programs `curry blumCode ⟨j+1, t⟩` (`t ≤ x`) on input `x`.  Each program is diagonalised
against at the first stage at which it becomes cheap, so `f i 0` and `f 0 0` differ at only
finitely many arguments; the parameter `t` lets one patch those finitely many arguments,
so that `f (j+1) t = f 0 0` for a suitable `t`.
-/

set_option maxHeartbeats 1000000

namespace CS

open Nat.Partrec Nat.Partrec.Code Primrec

/-! ### Generic form of the construction, parameterised by a cost function -/

/-- Maximal cost, according to `cf`, of the auxiliary programs with parameters `(j+1, t)`,
`t ≤ y`, on input `y`. -/

theorem primrec_okF :
    Primrec fun p : (Code × ℕ) × ℕ × ℕ × ℕ => okF p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2 := by
  have hstep : Primrec₂ fun (p : (Code × ℕ) × ℕ × ℕ × ℕ) (q : ℕ × Bool) =>
      ((!(decide (p.2.1 + 1 ≤ q.1.unpair.1.unpair.1) && decide (q.1.unpair.1.unpair.1 ≤ p.2.2.2) &&
            decide (q.1.unpair.2 ≤ p.2.2.2) && decide (q.1.unpair.1.unpair.2 ≤ q.1.unpair.2)))
        || (evaln p.1.2 p.1.1 q.1).isSome) && q.2 := by
    have hq : Primrec fun r : ((Code × ℕ) × ℕ × ℕ × ℕ) × ℕ × Bool => r.2.1 := fst.comp snd
    have hu1 : Primrec fun r : ((Code × ℕ) × ℕ × ℕ × ℕ) × ℕ × Bool => r.2.1.unpair.1.unpair.1 :=
      fst.comp (Primrec.unpair.comp (fst.comp (Primrec.unpair.comp hq)))
    have hu2 : Primrec fun r : ((Code × ℕ) × ℕ × ℕ × ℕ) × ℕ × Bool => r.2.1.unpair.1.unpair.2 :=
      snd.comp (Primrec.unpair.comp (fst.comp (Primrec.unpair.comp hq)))
    have hu3 : Primrec fun r : ((Code × ℕ) × ℕ × ℕ × ℕ) × ℕ × Bool => r.2.1.unpair.2 :=
      snd.comp (Primrec.unpair.comp hq)
    have hx : Primrec fun r : ((Code × ℕ) × ℕ × ℕ × ℕ) × ℕ × Bool => r.1.2.2.2 :=
      snd.comp (snd.comp (snd.comp fst))
    have hi : Primrec fun r : ((Code × ℕ) × ℕ × ℕ × ℕ) × ℕ × Bool => r.1.2.1 :=
      fst.comp (snd.comp fst)
    have hev : Primrec fun r : ((Code × ℕ) × ℕ × ℕ × ℕ) × ℕ × Bool =>
        (evaln r.1.1.2 r.1.1.1 r.2.1).isSome :=
      option_isSome.comp (primrec_evaln.comp
        (((snd.comp (fst.comp fst)).pair (fst.comp (fst.comp fst))).pair hq))
    exact Primrec.and.comp
      (Primrec.or.comp (Primrec.not.comp (Primrec.and.comp (Primrec.and.comp (Primrec.and.comp
        (PrimrecPred.decide (PrimrecRel.comp nat_le (Primrec.succ.comp hi) hu1))
        (PrimrecPred.decide (PrimrecRel.comp nat_le hu1 hx)))
        (PrimrecPred.decide (PrimrecRel.comp nat_le hu3 hx)))
        (PrimrecPred.decide (PrimrecRel.comp nat_le hu2 hu3)))) hev) (snd.comp snd)
  have hx : Primrec fun p : (Code × ℕ) × ℕ × ℕ × ℕ => p.2.2.2 := snd.comp (snd.comp snd)
  have hbranch2 := Primrec.list_foldr
      (f := fun p : (Code × ℕ) × ℕ × ℕ × ℕ =>
        List.range (Nat.pair (Nat.pair p.2.2.2 p.2.2.2) p.2.2.2 + 1))
      (Primrec.list_range.comp (Primrec.succ.comp
        (Primrec₂.natPair.comp (Primrec₂.natPair.comp hx hx) hx))) (const true) hstep
  have hbranch1 : Primrec fun p : (Code × ℕ) × ℕ × ℕ × ℕ =>
      (evaln p.1.2 p.1.1 (Nat.pair (Nat.pair 0 0) p.2.2.2)).isSome :=
    option_isSome.comp (primrec_evaln.comp
      (((snd.comp fst).pair (fst.comp fst)).pair
        (Primrec₂.natPair.comp (Primrec₂.natPair.comp (const 0) (const 0)) hx)))
  exact Primrec.ite
    (PrimrecRel.comp nat_lt (snd.comp (snd.comp snd)) (fst.comp (snd.comp snd)))
    hbranch1 hbranch2

