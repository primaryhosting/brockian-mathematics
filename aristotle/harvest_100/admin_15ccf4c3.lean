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
theorem equidistribution_of_transitive_symmetry [Nonempty X] [MulAction.IsPretransitive G X]
    (x : X) (A : Finset X) :
    (({g : G | g • x ∈ A} : Finset G).card : ℝ) / Fintype.card G
      = (A.card : ℝ) / Fintype.card X := by
  have hs : 0 < ({g : G | g • x = x} : Finset G).card := by
    refine Finset.card_pos.2 ⟨1, ?_⟩
    simp
  have hX : 0 < Fintype.card X := Fintype.card_pos
  have hGcard := card_group_eq_card_mul_card_stabilizerFinset (G := G) x
  have hA := card_hits_eq_card_mul_card_stabilizerFinset (G := G) x A
  rw [hGcard, hA]
  push_cast
  rw [div_eq_div_iff]
  · ring
  · have : (0:ℝ) < Fintype.card X := by exact_mod_cast hX
    have hs' : (0:ℝ) < (({g : G | g • x = x} : Finset G).card : ℝ) := by exact_mod_cast hs
    positivity
  · exact Nat.cast_ne_zero.2 hX.ne'

omit [Fintype G] [DecidableEq X] in
/-- **Uniformity of invariant weights.**  Any invariant probability weighting of a finite
set carrying a transitive symmetry group is the uniform one. -/
theorem uniform_of_invariant_weight [Nonempty X] [MulAction.IsPretransitive G X]
    (w : X → ℝ) (hinv : ∀ (g : G) (y : X), w (g • y) = w y)
    (hsum : ∑ y, w y = 1) (x : X) :
    w x = 1 / Fintype.card X := by
  have hconst : ∀ y : X, w y = w x := by
    intro y
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G x y
    exact hinv g x
  have hX : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos (α := X)
  have : (Fintype.card X : ℝ) * w x = 1 := by
    rw [← hsum, Finset.sum_congr rfl (fun y _ => hconst y), Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
  field_simp at this ⊢
  linarith [this]

end EquidistributionUniformity
end Brockian

