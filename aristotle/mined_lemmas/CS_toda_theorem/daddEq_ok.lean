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


theorem daddEq_ok {Q : (Assign → Bool) → Prop} {s : ℕ} {d1 d2 : GapData} (n : ℕ)
    (k1 : d1.Ok Q s) (k2 : d2.Ok Q s) : (daddEq n d1 d2).Ok Q (4 * s + 6) := by
  have v1p := hasFml_view k1.hpos n d1.w 0
  have v1n := hasFml_view k1.hneg n d1.w 0
  have v2p := hasFml_view k2.hpos n d1.w 0
  have v2n := hasFml_view k2.hneg n d1.w 0
  have hvar : HasFml Q 1 (fun a : Assign => a (n + d1.w)) := HasFml.var _
  have hnvar : HasFml Q 2 (fun a : Assign => !a (n + d1.w)) := HasFml.not hvar
  refine ⟨?_, ?_, ?_⟩
  · exact HasFml.mono (HasFml.or (HasFml.and hnvar v1p) (HasFml.and hvar v2p)) (by omega)
  · exact HasFml.mono (HasFml.or (HasFml.and hnvar v1n) (HasFml.and hvar v2n)) (by omega)
  · intro a hp hn
    simp only [daddEq, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hp hn
    have d1d := k1.hdisj (fun i => if i < n then a i else if i < n + d1.w then a (i + 0) else false)
    have d2d := k2.hdisj (fun i => if i < n then a i else if i < n + d1.w then a (i + 0) else false)
    simp only [view] at hp hn d1d d2d
    rcases hp with ⟨hb1, hp⟩ | ⟨hb1, hp⟩ <;> rcases hn with ⟨hb2, hn⟩ | ⟨hb2, hn⟩
    · exact d1d hp hn
    · rw [hb1] at hb2; exact Bool.noConfusion hb2
    · rw [hb1] at hb2; exact Bool.noConfusion hb2
    · exact d2d hp hn

/-- The sum of two gap functions. -/
