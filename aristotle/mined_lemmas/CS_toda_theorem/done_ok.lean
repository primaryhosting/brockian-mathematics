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


theorem done_ok {Q : (Assign → Bool) → Prop} (n k : ℕ) : (done n k).Ok Q (3 * k + 1) :=
  ⟨by simpa [done] using (hasFml_zerosAt (Q := Q) n 0 k).mono (by omega),
    HasFml.mono (HasFml.const (Q := Q) false) (by omega),
    by intro a _ hb; simp [done] at hb⟩

/-! #### Negation -/

/-- The gap function with the opposite value. -/
