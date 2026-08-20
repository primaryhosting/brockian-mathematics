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

theorem card_group_eq_card_mul_card_stabilizerFinset [MulAction.IsPretransitive G X] (x : X) :
    Fintype.card G = Fintype.card X * ({g : G | g • x = x} : Finset G).card := by
  have hmaps : Set.MapsTo (fun g : G => g • x) (↑(Finset.univ : Finset G))
      (↑(Finset.univ : Finset X)) := fun g _ => Finset.mem_coe.2 (Finset.mem_univ _)
  have h := Finset.card_eq_sum_card_fiberwise hmaps
  have hcongr : ∀ y ∈ (Finset.univ : Finset X),
      ({g : G | g • x = y} : Finset G).card = ({g : G | g • x = x} : Finset G).card := by
    intro y _
    exact card_fiber_eq_card_stabilizerFinset x y (MulAction.exists_smul_eq G x y)
  rw [Finset.card_univ] at h
  rw [h, Finset.sum_congr rfl hcongr, Finset.sum_const, Finset.card_univ, smul_eq_mul]

omit [Fintype X] in
/-- Counting the group elements sending `x` into a subset `A`, fiberwise over `A`. -/
