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


theorem dadd_val (n : ℕ) (x : Assign) (d1 d2 : GapData)
    (h1 : ∀ a, d1.pos a = true → d1.neg a = true → False)
    (h2 : ∀ a, d2.pos a = true → d2.neg a = true → False) :
    (dadd n d1 d2).val n x = d1.val n x + d2.val n x := by
  have hd1 : ∀ a, (done n d1.w).pos a = true → (done n d1.w).neg a = true → False := by
    intro a _ hb; simp [done] at hb
  have hd2 : ∀ a, (done n d2.w).pos a = true → (done n d2.w).neg a = true → False := by
    intro a _ hb; simp [done] at hb
  rw [dadd, daddEq_val n x _ _ (by simp [dmul, done]),
    dmul_val n x d1 (done n d2.w) h1 hd2, dmul_val n x (done n d1.w) d2 hd1 h2,
    done_val, done_val]
  ring

