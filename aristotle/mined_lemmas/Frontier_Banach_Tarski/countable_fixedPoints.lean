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

theorem countable_fixedPoints {g : E3 ≃ₗᵢ[ℝ] E3} (hg : g ∈ CrossPreserving) (hne : g ≠ 1) :
    {x : E3 | ‖x‖ = 1 ∧ g x = x}.Countable := by
  rcases Set.eq_empty_or_nonempty {x : E3 | ‖x‖ = 1 ∧ g x = x} with h | ⟨u, hu⟩
  · rw [h]; exact Set.countable_empty
  · have hsub : {x : E3 | ‖x‖ = 1 ∧ g x = x} ⊆ {u, -u} := by
      intro v hv
      by_contra hcon
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hcon
      exact hne (eq_one_of_fixes_two hg hu.1 hv.1 (fun h => hcon.1 h.symm)
        (fun h => hcon.2 (by rw [h]; simp)) hu.2 hv.2)
    exact (Set.Finite.subset (Set.finite_insert u (Set.finite_singleton (-u))) hsub).countable

end BT

import RequestProject.BT.Basic
import RequestProject.BT.FreeComb

/-!
# Free actions of the free group of rank two are paradoxical

If a group `G` acting on `X` contains a free group of rank two acting freely on an invariant
subset `E`, then `E` is `G`-paradoxical.
-/

open Set Pointwise BT.FreeComb

namespace BT

/-- If the free group of rank two acts freely on an invariant set `E` (through a group `G`),
then `E` is `G`-paradoxical. -/
