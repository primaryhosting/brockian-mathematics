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


theorem dmul_ok {Q : (Assign → Bool) → Prop} {s : ℕ} {d1 d2 : GapData} (n : ℕ)
    (k1 : d1.Ok Q s) (k2 : d2.Ok Q s) : (dmul n d1 d2).Ok Q (8 * s + 3) := by
  have v1p := hasFml_view k1.hpos n d1.w 0
  have v1n := hasFml_view k1.hneg n d1.w 0
  have v2p := hasFml_view k2.hpos n d2.w d1.w
  have v2n := hasFml_view k2.hneg n d2.w d1.w
  refine ⟨?_, ?_, ?_⟩
  · exact HasFml.mono (HasFml.or (HasFml.and v1p v2p) (HasFml.and v1n v2n)) (by omega)
  · exact HasFml.mono (HasFml.or (HasFml.and v1p v2n) (HasFml.and v1n v2p)) (by omega)
  · intro a hp hn
    simp only [dmul, Bool.or_eq_true, Bool.and_eq_true] at hp hn
    have d1d := k1.hdisj (fun i => if i < n then a i else if i < n + d1.w then a (i + 0) else false)
    have d2d := k2.hdisj (fun i => if i < n then a i else if i < n + d2.w then a (i + d1.w) else false)
    simp only [view] at hp hn d1d d2d
    rcases hp with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩ <;> rcases hn with ⟨hn1, hn2⟩ | ⟨hn1, hn2⟩
    · exact d2d hp2 hn2
    · exact d1d hp1 hn1
    · exact d1d hn1 hp1
    · exact d2d hn2 hp2

/-! #### Exponential sums -/

/-- Summing a gap function (for inputs of length `n + v`) over all extensions of the
length-`n` input by `v` bits. -/
