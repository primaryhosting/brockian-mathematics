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
Gap functions (differences of witness counts) and their closure properties.
-/
import RequestProject.Toda.Framework

namespace CS

open scoped BigOperators

/-! ### Splitting witnesses -/


def val (d : GapData) (n : ℕ) (x : Assign) : ℤ := ∑ y : Fin d.w → Bool, d.wt (ext n d.w x y)

/-- Well-formedness: both predicates are computed by formulas of size at most `s`, and
they are disjoint. -/
structure Ok (Q : (Assign → Bool) → Prop) (s : ℕ) (d : GapData) : Prop where
  hpos : HasFml Q s d.pos
  hneg : HasFml Q s d.neg
  hdisj : ∀ a, d.pos a = true → d.neg a = true → False

