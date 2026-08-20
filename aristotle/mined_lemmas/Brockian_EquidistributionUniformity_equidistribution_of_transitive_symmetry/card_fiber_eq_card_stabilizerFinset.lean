import Brockian.EquidistributionUniformity

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
# Equidistribution from transitive symmetry

If a finite group `G` acts transitively on a finite set `X`, then the orbit map
`g ↦ g • x` distributes the group uniformly over `X`: for every subset `A` of `X`
the proportion of group elements `g` with `g • x ∈ A` equals `|A| / |X|`.

The main result `Brockian.EquidistributionUniformity.equidistribution_of_transitive_symmetry`
is stated unconditionally (transitivity is part of the hypotheses on the action; no
auxiliary result is assumed).
-/

open scoped BigOperators
open Finset MulAction

namespace Brockian
namespace EquidistributionUniformity

variable {G X : Type*} [Group G] [Fintype G] [MulAction G X] [Fintype X] [DecidableEq X]

omit [Fintype X] in
/-- The number of group elements moving `x` to a fixed point `y` in its orbit does not
depend on `y`. -/

theorem card_fiber_eq_card_stabilizerFinset (x y : X) (h : ∃ g₀ : G, g₀ • x = y) :
    ({g : G | g • x = y} : Finset G).card = ({g : G | g • x = x} : Finset G).card := by
  obtain ⟨g₀, rfl⟩ := h
  refine Finset.card_nbij' (fun g => g₀⁻¹ * g) (fun g => g₀ * g) ?_ ?_ ?_ ?_
  · intro g hg
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hg ⊢
    rw [mul_smul, hg, inv_smul_smul]
  · intro g hg
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hg ⊢
    rw [mul_smul, hg]
  · intro g _
    simp [mul_inv_cancel_left]
  · intro g _
    simp [inv_mul_cancel_left]

/-- Counting the group fiberwise over the (full) orbit of `x`. -/
