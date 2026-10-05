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


theorem done_val (n k : ℕ) (x : Assign) : (done n k).val n x = 1 := by
  show ∑ y : Fin k → Bool, (done n k).wt (ext n k x y) = 1
  rw [Finset.sum_eq_single (fun _ => false : Fin k → Bool)]
  · have h : zerosAt n 0 k (ext n k x (fun _ => false)) = true := by
      rw [zerosAt_ext (by omega)]
      intro j; rfl
    simp [wt, done, h]
  · intro b _ hb
    have h : zerosAt n 0 k (ext n k x b) = false := by
      rcases Bool.eq_false_or_eq_true (zerosAt n 0 k (ext n k x b)) with hcon | hcon
      · exfalso
        have hz := (zerosAt_ext (n := n) (off := 0) (len := k) (W := k) (by omega) x b).1 hcon
        exact hb (funext fun j => by simpa using hz ⟨j.1, j.2⟩)
      · exact hcon
    simp [wt, done, h]
  · intro h; exact absurd (Finset.mem_univ _) h

