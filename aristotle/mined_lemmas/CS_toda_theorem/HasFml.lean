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


theorem HasFml.rename {Q : (Assign → Bool) → Prop} {s : ℕ} {f : Assign → Bool}
    (h : HasFml Q s f) (σ : ℕ → ℕ) : HasFml Q (2 * s) (fun a => f (fun i => a (σ i))) := by
  have h2 := HasFml.subst h (t := 1) (g := fun i a => a (σ i)) (fun i => HasFml.var (σ i))
  exact HasFml.mono h2 (by omega)

/-! ### Truncation and extension of assignments -/

/-- Zero out all variables `≥ n`. -/
