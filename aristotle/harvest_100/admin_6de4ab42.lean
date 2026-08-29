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
# Sing Uniform Of Transitive
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionUniformity.sing_uniform_of_transitive
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sing Uniform Of Transitive
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionUniformity.sing_uniform_of_transitive
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open MulAction

namespace Brockian.EquidistributionUniformity

variable {G X : Type*} [Group G] [Fintype G] [MulAction G X] [Fintype X] [DecidableEq X]

/-- If `G` acts transitively on `X`, then for a base point `x₀` the fibre of the orbit map
`g ↦ g • x₀` over any point `y` has the same cardinality as the stabilizer of `x₀`. -/
theorem card_fiber_eq_card_stabilizer (htrans : ∀ x y : X, ∃ g : G, g • x = y) (x₀ y : X) :
    (Finset.univ.filter fun g : G => g • x₀ = y).card =
      Fintype.card (stabilizer G x₀) := by
  classical
  obtain ⟨g₀, hg₀⟩ := htrans x₀ y
  rw [Fintype.card_subtype]
  refine Finset.card_bij' (fun g _ => g₀⁻¹ * g) (fun g _ => g₀ * g) ?_ ?_ ?_ ?_
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    simp [mem_stabilizer_iff, mul_smul, hg, ← hg₀]
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    have hstab : g • x₀ = x₀ := hg
    simp [mul_smul, hstab, hg₀]
  · intro g _
    simp [mul_assoc]
  · intro g _
    simp [mul_assoc]

/-- **Uniformity of the orbit map for a transitive action.**
If a finite group `G` acts transitively on a finite set `X`, then for any base point `x₀`
each point `y ∈ X` is hit by exactly `|G| / |X|` group elements: the number of `g` with
`g • x₀ = y` is independent of `y`, i.e. the pushforward of the uniform distribution on `G`
under `g ↦ g • x₀` is the uniform distribution on `X`. -/
theorem sing_uniform_of_transitive (htrans : ∀ x y : X, ∃ g : G, g • x = y) (x₀ y : X) :
    (Finset.univ.filter fun g : G => g • x₀ = y).card * Fintype.card X = Fintype.card G := by
  classical
  have horbit : (orbit G x₀ : Set X) = Set.univ :=
    Set.eq_univ_of_forall fun z => htrans x₀ z
  have hcard : Fintype.card (orbit G x₀) = Fintype.card X := by
    rw [Fintype.card_eq_nat_card, Nat.card_coe_set_eq, horbit, Set.ncard_univ,
      Nat.card_eq_fintype_card]
  have hos := MulAction.card_orbit_mul_card_stabilizer_eq_card_group G x₀
  rw [card_fiber_eq_card_stabilizer htrans x₀ y, ← hcard, mul_comm]
  exact hos

/-- Probabilistic form: for a transitive action, the proportion of group elements sending the
base point `x₀` to a given point `y` equals `1 / |X|`. -/
theorem sing_uniform_ratio_of_transitive (htrans : ∀ x y : X, ∃ g : G, g • x = y) (x₀ y : X) :
    ((Finset.univ.filter fun g : G => g • x₀ = y).card : ℚ) / Fintype.card G =
      1 / Fintype.card X := by
  have hG : (0 : ℚ) < Fintype.card G := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨(1 : G)⟩
  have hX : (0 : ℚ) < Fintype.card X := by
    have : Nonempty X := ⟨x₀⟩
    exact_mod_cast Fintype.card_pos_iff.mpr this
  have h := sing_uniform_of_transitive htrans x₀ y
  have h' : ((Finset.univ.filter fun g : G => g • x₀ = y).card : ℚ) * Fintype.card X =
      Fintype.card G := by exact_mod_cast h
  field_simp
  linarith [h']

end Brockian.EquidistributionUniformity

