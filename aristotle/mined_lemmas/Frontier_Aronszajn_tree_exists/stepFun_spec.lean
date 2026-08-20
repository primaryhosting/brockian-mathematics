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


theorem stepFun_spec {a : Ordinal.{0}} {d : Ordinal.{0} → Ordinal.{0} → ℕ}
    (h : ∃ f, Nice a f ∧ ∀ b < a, Coh f (d b) b) :
    Nice a (stepFun a d) ∧ ∀ b < a, Coh (stepFun a d) (d b) b := by
  classical
  rw [stepFun, dif_pos h]
  exact h.choose_spec

open Classical in
/-- The coherent sequence of partial injections. -/
