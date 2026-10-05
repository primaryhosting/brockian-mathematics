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
# Equidistribution Of Transitive Symmetry
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionUniformity.equidistribution_of_transitive_symmetry
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

namespace Brockian
namespace EquidistributionUniformity

open Finset

variable {G X : Type*} [Group G] [Fintype G] [MulAction G X] [Fintype X] [DecidableEq X]

omit [Fintype X] in
/-- All fibers of the orbit map `g ↦ g • x` have the same cardinality, namely that of the
stabilizer fiber `{g | g • x = x}`, provided the point `y` lies in the orbit of `x`. -/
theorem card_fiber_eq_card_stabilizer_fiber (x y : X) (hxy : ∃ g : G, g • x = y) :
    #{g : G | g • x = y} = #{g : G | g • x = x} := by
  obtain ⟨g₀, hg₀⟩ := hxy
  refine Finset.card_nbij (fun g => g₀⁻¹ * g) ?_ ?_ ?_
  · intro g hg
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hg ⊢
    rw [mul_smul, hg, ← hg₀, inv_smul_smul]
  · intro a _ b _ hab
    exact mul_left_cancel hab
  · intro g hg
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hg
    refine ⟨g₀ * g, ?_, ?_⟩
    · simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and]
      rw [mul_smul, hg, hg₀]
    · simp

/-- Counting `G` fiberwise over the orbit map `g ↦ g • x`. -/
theorem card_group_eq_card_mul_card_stabilizer_fiber
    (htrans : ∀ x y : X, ∃ g : G, g • x = y) (x : X) :
    Fintype.card G = Fintype.card X * #{g : G | g • x = x} := by
  have h : (Finset.univ : Finset G).card
      = ∑ y ∈ (Finset.univ : Finset X), #{g ∈ (Finset.univ : Finset G) | g • x = y} :=
    Finset.card_eq_sum_card_fiberwise (fun g _ => Finset.mem_univ (g • x))
  rw [Finset.card_univ] at h
  rw [h, Finset.sum_congr rfl (fun y _ => card_fiber_eq_card_stabilizer_fiber x y (htrans x y)),
    Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- **Equidistribution of a transitive symmetry group.**

If a finite group `G` acts transitively on a finite set `X`, then for any point `x : X` and any
subset `S ⊆ X`, the group elements sending `x` into `S` are exactly a `#S / #X` fraction of `G`:
`#{g | g • x ∈ S} * #X = #S * #G`.

Thus the orbit map `g ↦ g • x` equidistributes `G` over `X`; no additional hypothesis beyond
transitivity is needed. -/
theorem equidistribution_of_transitive_symmetry
    (htrans : ∀ x y : X, ∃ g : G, g • x = y) (x : X) (S : Finset X) :
    #{g : G | g • x ∈ S} * Fintype.card X = S.card * Fintype.card G := by
  have hfib : #{g : G | g • x ∈ S} = S.card * #{g : G | g • x = x} := by
    have h : #{g : G | g • x ∈ S}
        = ∑ y ∈ S, #{g ∈ ({g : G | g • x ∈ S} : Finset G) | g • x = y} := by
      refine Finset.card_eq_sum_card_fiberwise ?_
      intro g hg
      simpa using (Finset.mem_filter.mp hg).2
    have h2 : ∀ y ∈ S, #{g ∈ ({g : G | g • x ∈ S} : Finset G) | g • x = y}
        = #{g : G | g • x = x} := by
      intro y hy
      have hset : {g ∈ ({g : G | g • x ∈ S} : Finset G) | g • x = y}
          = ({g : G | g • x = y} : Finset G) := by
        ext g
        constructor
        · intro hg
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ g, (Finset.mem_filter.mp hg).2⟩
        · intro hg
          have hgy : g • x = y := (Finset.mem_filter.mp hg).2
          refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ g, ?_⟩, hgy⟩
          rw [hgy]; exact hy
      rw [hset]
      exact card_fiber_eq_card_stabilizer_fiber x y (htrans x y)
    rw [h, Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul]
  rw [hfib, card_group_eq_card_mul_card_stabilizer_fiber htrans x]
  ring

/-- Rational-density form of the equidistribution statement: the proportion of `g ∈ G` with
`g • x ∈ S` equals the density `#S / #X`. -/
theorem equidistribution_density_of_transitive_symmetry
    (htrans : ∀ x y : X, ∃ g : G, g • x = y) (x : X) (S : Finset X) :
    (#{g : G | g • x ∈ S} : ℚ) / (Fintype.card G : ℚ)
      = (S.card : ℚ) / (Fintype.card X : ℚ) := by
  have hX : (0 : ℚ) < Fintype.card X := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨x⟩
  have hG : (0 : ℚ) < Fintype.card G := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨1⟩
  have h := equidistribution_of_transitive_symmetry htrans x S
  have h' : (#{g : G | g • x ∈ S} : ℚ) * (Fintype.card X : ℚ)
      = (S.card : ℚ) * (Fintype.card G : ℚ) := by exact_mod_cast h
  field_simp
  linarith [h']

/-- Version of `equidistribution_of_transitive_symmetry` phrased with Mathlib's
`MulAction.IsPretransitive` typeclass. -/
theorem equidistribution_of_isPretransitive [MulAction.IsPretransitive G X]
    (x : X) (S : Finset X) :
    #{g : G | g • x ∈ S} * Fintype.card X = S.card * Fintype.card G :=
  equidistribution_of_transitive_symmetry
    (fun a b => MulAction.exists_smul_eq G a b) x S

end EquidistributionUniformity
end Brockian

