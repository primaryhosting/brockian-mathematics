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


theorem nice_zero : Nice 0 (fun _ => 0) := by
  refine ⟨fun b hb => absurd hb (by simp), fun b _ => rfl, ?_⟩
  have : {n : ℕ | ∀ b < (0 : Ordinal.{0}), (0 : ℕ) ≠ n} = Set.univ := by
    ext n; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact fun b hb => absurd hb (by simp)
  rw [CoInf, this]
  exact Set.infinite_univ

/-! ### The successor step -/

