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
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian
namespace EquidistributionUniformity

open MulAction

/-- The set of group elements moving `x` to `y` is a left coset of the stabilizer of `x`,
hence has the same cardinality as the stabilizer, provided some element does move `x` to `y`. -/
theorem card_filter_smul_eq_card_stabilizer {G X : Type*} [Group G] [Fintype G] [MulAction G X]
    [DecidableEq X] (x y : X) (g₀ : G) (hg₀ : g₀ • x = y) :
    (Finset.univ.filter fun g : G => g • x = y).card
      = Fintype.card (MulAction.stabilizer G x) := by
  subst hg₀
  rw [Fintype.card_subtype]
  refine Finset.card_nbij' (fun g => g₀⁻¹ * g) (fun h => g₀ * h) ?_ ?_ ?_ ?_
  · intro g hg
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at *
    simp [MulAction.mem_stabilizer_iff, mul_smul, hg]
  · intro h hh
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and,
      MulAction.mem_stabilizer_iff] at *
    simp [mul_smul, hh]
  · intro g _; simp
  · intro h _; simp

/-- **Uniformity of singleton frequencies for a transitive action.**

If a finite group `G` acts transitively on a finite type `X`, then for every base point `x`
and every target point `y` the number of group elements sending `x` to `y` is the same for
all `y`, namely `|G| / |X|`; equivalently, `#{g | g • x = y} * |X| = |G|`.

In probabilistic terms: pushing the uniform distribution on `G` forward along the orbit map
`g ↦ g • x` yields the uniform distribution on `X`, each singleton `{y}` receiving mass
`1 / |X|`.

The transitivity hypothesis is supplied as the instance `[MulAction.IsPretransitive G X]`. -/
theorem sing_uniform_of_transitive {G X : Type*} [Group G] [Fintype G] [MulAction G X]
    [Fintype X] [DecidableEq X] [MulAction.IsPretransitive G X] (x y : X) :
    (Finset.univ.filter fun g : G => g • x = y).card * Fintype.card X = Fintype.card G := by
  obtain ⟨g₀, hg₀⟩ := MulAction.exists_smul_eq G x y
  rw [card_filter_smul_eq_card_stabilizer x y g₀ hg₀]
  haveI : Fintype (MulAction.orbit G x) := Set.Finite.fintype (Set.toFinite _)
  have horb : Fintype.card (MulAction.orbit G x) = Fintype.card X := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, MulAction.orbit_eq_univ G x,
      Nat.card_coe_set_eq, Set.ncard_univ]
  calc Fintype.card (MulAction.stabilizer G x) * Fintype.card X
      = Fintype.card (MulAction.orbit G x) * Fintype.card (MulAction.stabilizer G x) := by
        rw [horb, Nat.mul_comm]
    _ = Fintype.card G := MulAction.card_orbit_mul_card_stabilizer_eq_card_group G x

/-- Real-valued form: the pushforward of the uniform measure on `G` under `g ↦ g • x`
assigns mass exactly `1 / |X|` to each singleton `{y}`. -/
theorem sing_uniform_ratio_of_transitive {G X : Type*} [Group G] [Fintype G]
    [MulAction G X] [Fintype X] [DecidableEq X] [MulAction.IsPretransitive G X] (x y : X) :
    ((Finset.univ.filter fun g : G => g • x = y).card : ℝ) / (Fintype.card G : ℝ)
      = 1 / (Fintype.card X : ℝ) := by
  have hG : (Fintype.card G : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := G))
  have hX : (Fintype.card X : ℝ) ≠ 0 := by
    have : Nonempty X := ⟨x⟩
    exact_mod_cast (Fintype.card_ne_zero (α := X))
  have h := sing_uniform_of_transitive (G := G) x y
  have h' : ((Finset.univ.filter fun g : G => g • x = y).card : ℝ) * (Fintype.card X : ℝ)
      = (Fintype.card G : ℝ) := by exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) h
  field_simp
  linarith [h']

/-- Hypothesis form of `sing_uniform_of_transitive`: transitivity of the action is given as an
ordinary hypothesis `htrans` rather than as a typeclass instance. -/
theorem sing_uniform_of_forall_exists_smul_eq {G X : Type*} [Group G] [Fintype G] [MulAction G X]
    [Fintype X] [DecidableEq X] (htrans : ∀ a b : X, ∃ g : G, g • a = b) (x y : X) :
    (Finset.univ.filter fun g : G => g • x = y).card * Fintype.card X = Fintype.card G := by
  haveI : MulAction.IsPretransitive G X := ⟨fun a b => htrans a b⟩
  exact sing_uniform_of_transitive x y

end EquidistributionUniformity
end Brockian

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

