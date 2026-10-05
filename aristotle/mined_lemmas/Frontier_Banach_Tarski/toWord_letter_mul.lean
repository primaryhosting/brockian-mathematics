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

lemma toWord_letter_mul {p : α × Bool} {w : FreeGroup α}
    (h : ∀ q, w.toWord.head? = some q → (p.1 = q.1 → p.2 = q.2)) :
    (FreeGroup.mk [p] * w).toWord = p :: w.toWord := by
  have h1 : FreeGroup.mk [p] * w = FreeGroup.mk (p :: w.toWord) := by
    rw [← FreeGroup.mk_toWord (x := w), FreeGroup.mul_mk]; simp
  rw [h1, FreeGroup.toWord_mk]
  refine FreeGroup.IsReduced.reduce_eq ?_
  cases hw : w.toWord with
  | nil => simp
  | cons q t =>
      rw [FreeGroup.isReduced_cons_cons]
      refine ⟨h q (by simp [hw]), ?_⟩
      rw [← hw]; exact FreeGroup.isReduced_toWord

/-- Multiplying on the left by the inverse of the first letter deletes it. -/
