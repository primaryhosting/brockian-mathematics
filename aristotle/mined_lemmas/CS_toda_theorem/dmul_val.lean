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


theorem dmul_val (n : ℕ) (x : Assign) (d1 d2 : GapData)
    (h1 : ∀ a, d1.pos a = true → d1.neg a = true → False)
    (h2 : ∀ a, d2.pos a = true → d2.neg a = true → False) :
    (dmul n d1 d2).val n x = d1.val n x * d2.val n x := by
  show ∑ y : Fin (d1.w + d2.w) → Bool, (dmul n d1 d2).wt (ext n (d1.w + d2.w) x y) = _
  rw [sum_split d1.w d2.w, val, val, Fintype.sum_mul_sum]
  refine Finset.sum_congr rfl fun y1 _ => Finset.sum_congr rfl fun y2 _ => ?_
  have e1 : ∀ f : Assign → Bool,
      view n d1.w 0 f (ext n (d1.w + d2.w) x (Fin.append y1 y2)) = f (ext n d1.w x y1) := by
    intro f
    rw [view_ext (by omega) f x (Fin.append y1 y2), subw_append_left]
  have e2 : ∀ f : Assign → Bool,
      view n d2.w d1.w f (ext n (d1.w + d2.w) x (Fin.append y1 y2)) = f (ext n d2.w x y2) := by
    intro f
    rw [view_ext (by omega) f x (Fin.append y1 y2), subw_append_right]
  simp only [wt, dmul, e1, e2]
  exact wt_mul_aux _ _ _ _ (h1 _) (h2 _)

