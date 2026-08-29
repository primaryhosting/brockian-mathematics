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

theorem primrec_MF : Primrec fun p : (Code × ℕ) × ℕ × ℕ => MF p.1.1 p.1.2 p.2.1 p.2.2 := by
  have hrange : Primrec fun p : (Code × ℕ) × ℕ × ℕ => List.range (p.2.2 + 1) :=
    Primrec.list_range.comp (Primrec.succ.comp (snd.comp snd))
  have hstep : Primrec₂ fun (p : (Code × ℕ) × ℕ × ℕ) (q : ℕ × ℕ) =>
      max (costF p.1.1 (Nat.pair (Nat.pair (p.2.1 + 1) q.1) p.2.2) p.1.2) q.2 := by
    have hcost : Primrec fun r : ((Code × ℕ) × ℕ × ℕ) × ℕ × ℕ =>
        costF r.1.1.1 (Nat.pair (Nat.pair (r.1.2.1 + 1) r.2.1) r.1.2.2) r.1.1.2 :=
      primrec_costF.comp
        ((fst.comp (fst.comp fst)).pair
          (Primrec₂.natPair.comp
            (Primrec₂.natPair.comp (Primrec.succ.comp (fst.comp (snd.comp fst)))
              (fst.comp snd))
            (snd.comp (snd.comp fst))))
        (snd.comp (fst.comp fst))
    exact Primrec.nat_max.comp hcost (snd.comp snd)
  exact Primrec.list_foldr hrange (const 0) hstep

