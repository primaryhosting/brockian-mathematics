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


theorem dmul_disj (n : ℕ) {d1 d2 : GapData} (h1 : Disj d1) (h2 : Disj d2) :
    Disj (dmul n d1 d2) := by
  intro a hp hn
  simp only [dmul, Bool.or_eq_true, Bool.and_eq_true] at hp hn
  have d1d := h1 (fun i => if i < n then a i else if i < n + d1.w then a (i + 0) else false)
  have d2d := h2 (fun i => if i < n then a i else if i < n + d2.w then a (i + d1.w) else false)
  simp only [view] at hp hn d1d d2d
  rcases hp with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩ <;> rcases hn with ⟨hn1, hn2⟩ | ⟨hn1, hn2⟩
  · exact d2d hp2 hn2
  · exact d1d hp1 hn1
  · exact d1d hn1 hp1
  · exact d2d hn2 hp2

/-- The product of the `2 ^ d` gap functions `D off, …, D (off + 2 ^ d - 1)`, computed by a
balanced binary tree (so that the formula size stays polynomial). -/
