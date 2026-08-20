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

/-
The limit step of the transfinite construction: at a countable limit ordinal `a`
we build a nice partial injection with domain `a` coherent with all previous ones,
by an `ω`-recursion along a cofinal sequence, reserving one new value at each stage
so that the resulting function still omits infinitely many naturals.
-/
import RequestProject.Aronszajn.Step

open Ordinal Cardinal Set

namespace Aronszajn


theorem restrict_mem {x : TreeNode} {b : Ordinal.{0}} (hb : b < tlvl x) :
    (b, fun e => if e < b then x.1.2 e else 0) ∈ TreeSet := by
  classical
  refine ⟨hb.trans (tlvl_lt_omega1 x), ?_, ?_, ?_⟩
  · intro e he f hf hef
    simp only [if_pos he, if_pos hf] at hef
    exact injBelow_node x e (he.trans hb) f (hf.trans hb) hef
  · intro e hbe
    simp [not_lt.2 hbe]
  · refine Coh.trans (g := x.1.2) (coh_of_eq ?_) ?_
    · intro e he; simp [he]
    · exact ((coh_node x).mono hb.le).trans
        ((E_spec (tlvl x) (tlvl_lt_omega1 x)).2 b hb)

