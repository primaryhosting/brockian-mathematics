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


theorem succ_lt_omega1 {a : Ordinal.{0}} (h : a < ω₁) : a + 1 < ω₁ :=
  (Cardinal.isSuccLimit_omega 1).succ_lt h

end Aronszajn

/-
The successor and limit steps of the transfinite construction of a coherent
sequence of partial injections.
-/
import RequestProject.Aronszajn.Extend

open Ordinal Cardinal Set

namespace Aronszajn

/-! ### The zero step -/

