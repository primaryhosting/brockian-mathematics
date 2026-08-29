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


theorem daddEq_val (n : ℕ) (x : Assign) (d1 d2 : GapData) (hw : d2.w = d1.w) :
    (daddEq n d1 d2).val n x = d1.val n x + d2.val n x := by
  obtain ⟨w2, p2, q2⟩ := d2
  simp only at hw
  subst hw
  show ∑ y : Fin (d1.w + 1) → Bool, (daddEq n d1 ⟨d1.w, p2, q2⟩).wt (ext n (d1.w + 1) x y) = _
  rw [sum_split d1.w 1, val, val, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y1 _ => ?_
  rw [sum_fin_one_bool]
  have hb : ∀ b : Fin 1 → Bool,
      ext n (d1.w + 1) x (Fin.append y1 b) (n + d1.w) = b ⟨0, by omega⟩ := by
    intro b
    rw [ext_ge (by omega)]
    exact append_apply_right y1 b _ _ (by simp)
  have e1 : ∀ (f : Assign → Bool) (b : Fin 1 → Bool),
      view n d1.w 0 f (ext n (d1.w + 1) x (Fin.append y1 b)) = f (ext n d1.w x y1) := by
    intro f b
    rw [view_ext (by omega) f x (Fin.append y1 b), subw_append_left]
  simp only [wt, daddEq, hb, e1]
  simp

