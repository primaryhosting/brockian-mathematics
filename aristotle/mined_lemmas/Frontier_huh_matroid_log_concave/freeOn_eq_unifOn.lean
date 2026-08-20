import RequestProject.Main

/-!
# Log-concavity of the characteristic polynomial of a uniform matroid

This file constructs the uniform matroid `U_{r,E}` on a finite ground set `E` and proves that
the coefficients of its characteristic polynomial form a log-concave sequence, i.e. the
Adiprasito–Huh–Katz theorem for uniform matroids.
-/

namespace Frontier

open Finset Polynomial

variable {α : Type*}

/-- The uniform matroid `U_{r,E}`: the independent sets are the subsets of `E` of size at most
`r`. -/

theorem freeOn_eq_unifOn (E : Finset α) : Matroid.freeOn (E : Set α) = unifOn E E.card := by
  refine Matroid.ext_indep ?_ fun I hI => ?_
  · simp [unifOn]
  · rw [Matroid.freeOn_indep_iff, unifOn_indep_iff]
    simp only [Matroid.freeOn_ground] at hI
    have hcard : I.ncard ≤ E.card := by
      simpa [Set.ncard_coe_finset] using Set.ncard_le_ncard hI E.finite_toSet
    simp [hI, hcard]

/-! ### A sanity check

For the uniform matroid `U_{2,3}` (three points on a line) the characteristic polynomial is
`t^2 - 3t + 2`, so the Whitney numbers are `w_2 = 1`, `w_1 = 3`, `w_0 = 2`. -/

example : whitneyAbs (unifOn ({0, 1, 2} : Finset ℕ) 2) ({0, 1, 2} : Finset ℕ) 2 = 1 := by
  rw [whitneyAbs_unifOn_pos _ _ _ (by decide) (by norm_num)]
  decide

example : whitneyAbs (unifOn ({0, 1, 2} : Finset ℕ) 2) ({0, 1, 2} : Finset ℕ) 1 = 3 := by
  rw [whitneyAbs_unifOn_pos _ _ _ (by decide) (by norm_num)]
  decide

example : whitneyAbs (unifOn ({0, 1, 2} : Finset ℕ) 2) ({0, 1, 2} : Finset ℕ) 0 = 2 := by
  rw [whitneyAbs_unifOn_zero _ _ (by decide) (by norm_num)]
  decide

end Frontier

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

namespace Frontier

open Finset Polynomial

variable {α : Type*}

/-- The rank of a set in a matroid, as a natural number. -/
