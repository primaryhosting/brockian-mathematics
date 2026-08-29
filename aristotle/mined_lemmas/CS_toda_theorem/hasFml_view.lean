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


theorem hasFml_view {Q : (Assign → Bool) → Prop} {s : ℕ} {f : Assign → Bool}
    (h : HasFml Q s f) (n w k : ℕ) : HasFml Q (2 * s) (view n w k f) := by
  have hg : ∀ i : ℕ, HasFml Q 1
      (fun a : Assign => if i < n then a i else if i < n + w then a (i + k) else false) := by
    intro i
    by_cases h1 : i < n
    · simpa [h1] using HasFml.var i
    · by_cases h2 : i < n + w
      · simpa [h1, h2] using HasFml.var (i + k)
      · simpa [h1, h2] using HasFml.const (Q := Q) false
  have := HasFml.subst h hg
  exact HasFml.mono this (by omega)

