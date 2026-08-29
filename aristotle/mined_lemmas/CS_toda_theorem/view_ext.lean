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


theorem view_ext {n w k W : ℕ} (h : k + w ≤ W) (f : Assign → Bool) (x : Assign)
    (y : Fin W → Bool) :
    view n w k f (ext n W x y) = f (ext n w x (subw k w W h y)) := by
  unfold view
  congr 1
  funext i
  by_cases h1 : i < n
  · simp [h1, ext_lt h1]
  · by_cases h2 : i < n + w
    · have hiw : i - n < w := by omega
      have hik : i + k = n + (k + (i - n)) := by omega
      have hlt : k + (i - n) < W := by omega
      rw [if_neg h1, if_pos h2, hik, ext_ge hlt]
      rw [ext]
      simp only [dif_neg h1, dif_pos hiw]
      simp [subw]
    · have hiw : ¬ (i - n < w) := by omega
      rw [if_neg h1, if_neg h2]
      rw [ext]
      simp [h1, hiw]

/-! ### Big conjunctions -/

/-- Conjunction of a list of Boolean functions. -/
