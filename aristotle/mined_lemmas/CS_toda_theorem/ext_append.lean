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


theorem ext_append (n w v : ℕ) (x : Assign) (y : Fin w → Bool) (z : Fin v → Bool) :
    ext n (w + v) x (Fin.append y z) = ext (n + w) v (ext n w x y) z := by
  funext i
  by_cases h : i < n
  · have h' : i < n + w := by omega
    simp [ext, h, h']
  · by_cases h2 : i - n < w
    · have h3 : i < n + w := by omega
      have h4 : i - n < w + v := by omega
      simp only [ext, dif_neg h, dif_pos h4, dif_pos h3]
      have hidx : (⟨i - n, h4⟩ : Fin (w + v)) = Fin.castAdd v ⟨i - n, h2⟩ := by
        apply Fin.ext; simp
      rw [hidx, Fin.append_left, dif_pos h2]
    · by_cases h5 : i - n < w + v
      · have h6 : ¬ (i < n + w) := by omega
        have h7 : i - (n + w) < v := by omega
        simp only [ext, dif_neg h, dif_pos h5, dif_neg h6, dif_pos h7]
        have hidx : (⟨i - n, h5⟩ : Fin (w + v)) = Fin.natAdd w ⟨i - (n + w), h7⟩ := by
          apply Fin.ext; simp; omega
        rw [hidx, Fin.append_right]
      · have h6 : ¬ (i < n + w) := by omega
        have h7 : ¬ (i - (n + w) < v) := by omega
        simp [ext, h, h5, h6, h7]

/-! ### Languages and complexity classes -/

/-- A language: `L n x` says that the length-`n` input `x` (given by the variables
`0, …, n-1`) belongs to the language. -/
