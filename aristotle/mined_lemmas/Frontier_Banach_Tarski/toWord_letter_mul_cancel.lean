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

import Mathlib

/-!
# Rotations of three dimensional Euclidean space

Explicit rotations about the `z`- and `x`-axes, the cross product, and the fact that a
nontrivial rotation fixes at most two points of the unit sphere.
-/

open scoped RealInnerProductSpace

namespace BT

/-- Three dimensional Euclidean space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- A vector of `E3` given by its three coordinates. -/

lemma toWord_letter_mul_cancel {p : α × Bool} {t : List (α × Bool)} {w : FreeGroup α}
    (hw : w.toWord = (p.1, !p.2) :: t) :
    (FreeGroup.mk [p] * w).toWord = t := by
  have h1 : FreeGroup.mk [p] * w = FreeGroup.mk (p :: (p.1, !p.2) :: t) := by
    rw [← FreeGroup.mk_toWord (x := w), hw, FreeGroup.mul_mk]; simp
  have h2 : FreeGroup.mk (p :: (p.1, !p.2) :: t) = FreeGroup.mk t := by
    have hstep : FreeGroup.Red.Step (p :: (p.1, !p.2) :: t) t := by
      have := @FreeGroup.Red.Step.not α [] t p.1 p.2
      simpa using this
    exact Quot.sound hstep
  have h3 : FreeGroup.IsReduced t := by
    have hred := FreeGroup.isReduced_toWord (x := w)
    rw [hw] at hred
    exact hred.infix (List.infix_cons (List.infix_refl t))
  rw [h1, h2, FreeGroup.toWord_mk, h3.reduce_eq]

end Words

/-- The set of elements whose reduced word starts with the letter `p`. -/
