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


def SigmaC (Q : (Assign → Bool) → Prop) : ℕ → Lang → Prop
  | 0, L => InP Q L
  | (k + 1), L =>
      ∃ (M : Lang) (w : ℕ → ℕ), IsPolyBound w ∧ SigmaC Q k (fun n x => ¬ M n x) ∧
        ∀ n x, L n x ↔ ∃ y : Fin (w n) → Bool, M (n + w n) (ext n (w n) x y)

/-- The polynomial hierarchy. -/
