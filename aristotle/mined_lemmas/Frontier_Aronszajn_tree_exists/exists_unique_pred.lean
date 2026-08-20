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


theorem exists_unique_pred (x : TreeNode) {b : Ordinal.{0}} (hb : b < tlvl x) :
    ∃! y : TreeNode, tle y x ∧ tlvl y = b := by
  classical
  refine ⟨⟨_, restrict_mem hb⟩, ⟨⟨hb.le, ?_⟩, rfl⟩, ?_⟩
  · intro e he
    change (if e < b then x.1.2 e else 0) = x.1.2 e
    simp only [tlvl] at he
    simp [he]
  · rintro y ⟨hy, hylvl⟩
    refine node_ext (by rw [hylvl]; rfl) ?_
    intro e he
    rw [hy.2 e he]
    change x.1.2 e = if e < b then x.1.2 e else 0
    rw [hylvl] at he
    simp [he]

/-! ### Every level is countable -/

