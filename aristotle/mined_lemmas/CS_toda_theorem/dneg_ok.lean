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


theorem dneg_ok {Q : (Assign → Bool) → Prop} {s : ℕ} {d : GapData} (h : d.Ok Q s) :
    (dneg d).Ok Q s :=
  ⟨h.hneg, h.hpos, fun a h1 h2 => h.hdisj a h2 h1⟩

/-! #### Products -/

/-- The product of two gap functions: the witness is the concatenation of the two
witnesses. -/
