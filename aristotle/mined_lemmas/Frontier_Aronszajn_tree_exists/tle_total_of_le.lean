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


theorem tle_total_of_le {x y z : TreeNode} (hy : tle y x) (hz : tle z x) : tle y z ∨ tle z y := by
  rcases le_total (tlvl y) (tlvl z) with h | h
  · exact Or.inl ⟨h, fun e he => by rw [hy.2 e he, ← hz.2 e (lt_of_lt_of_le he h)]⟩
  · exact Or.inr ⟨h, fun e he => by rw [hz.2 e he, ← hy.2 e (lt_of_lt_of_le he h)]⟩

/-- The restriction of a node to a smaller level is again a node. -/
