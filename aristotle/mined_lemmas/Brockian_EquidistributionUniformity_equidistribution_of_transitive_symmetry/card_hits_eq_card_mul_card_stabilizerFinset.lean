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

theorem card_hits_eq_card_mul_card_stabilizerFinset [MulAction.IsPretransitive G X]
    (x : X) (A : Finset X) :
    ({g : G | g • x ∈ A} : Finset G).card = A.card * ({g : G | g • x = x} : Finset G).card := by
  have hmaps : Set.MapsTo (fun g : G => g • x)
      (↑({g : G | g • x ∈ A} : Finset G)) (↑A) := by
    intro g hg
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hg
    exact hg
  have h := Finset.card_eq_sum_card_fiberwise hmaps
  have hcongr : ∀ y ∈ A,
      ({g ∈ ({g : G | g • x ∈ A} : Finset G) | g • x = y}).card
        = ({g : G | g • x = x} : Finset G).card := by
    intro y hy
    have hfil : ({g ∈ ({g : G | g • x ∈ A} : Finset G) | g • x = y})
        = ({g : G | g • x = y} : Finset G) := by
      ext g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨-, hgy⟩; exact hgy
      · rintro hgy; exact ⟨hgy ▸ hy, hgy⟩
    rw [hfil]
    exact card_fiber_eq_card_stabilizerFinset x y (MulAction.exists_smul_eq G x y)
  rw [h, Finset.sum_congr rfl hcongr, Finset.sum_const, smul_eq_mul]

/-- **Equidistribution from transitive symmetry.**  If a finite group `G` acts
transitively on a finite nonempty set `X`, then for every base point `x` and every
subset `A ⊆ X`, the fraction of group elements `g` with `g • x ∈ A` is exactly the
density `|A| / |X|` of `A` in `X`. -/
