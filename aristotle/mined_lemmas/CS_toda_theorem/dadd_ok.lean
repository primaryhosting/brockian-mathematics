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


theorem dadd_ok {Q : (Assign → Bool) → Prop} {s W : ℕ} {d1 d2 : GapData} (n : ℕ)
    (k1 : d1.Ok Q s) (k2 : d2.Ok Q s) (hw1 : d1.w ≤ W) (hw2 : d2.w ≤ W) :
    (dadd n d1 d2).Ok Q (32 * (s + 3 * W + 1) + 18) := by
  set s' := s + 3 * W + 1 with hs'
  have k1' : d1.Ok Q s' := k1.mono (by omega)
  have k2' : d2.Ok Q s' := k2.mono (by omega)
  have e1 : (done n d2.w).Ok Q s' := (done_ok n d2.w).mono (by omega)
  have e2 : (done n d1.w).Ok Q s' := (done_ok n d1.w).mono (by omega)
  have m1 := dmul_ok (Q := Q) (s := s') n k1' e1
  have m2 := dmul_ok (Q := Q) (s := s') n e2 k2'
  have := daddEq_ok (Q := Q) (s := 8 * s' + 3) n m1 m2
  exact this.mono (by omega)

