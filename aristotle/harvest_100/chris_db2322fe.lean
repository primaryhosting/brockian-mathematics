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
# Equidistribution Of Transitive Symmetry
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionUniformity.equidistribution_of_transitive_symmetry
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Equidistribution Of Transitive Symmetry

If a group `G` acts transitively on a set `X`, then the group elements are equidistributed over
the points of `X`: for a fixed base point `x`, each target point `y` is hit by exactly
`Nat.card G / Nat.card X` group elements.  The equidistribution property, which is elsewhere
taken as a hypothesis, is proved here outright from transitivity via the orbit-stabilizer
theorem.
-/

namespace Brockian
namespace EquidistributionUniformity

open MulAction

variable {G X : Type*} [Group G] [MulAction G X]

/-- The *transporter* from `x` to `y`: the set of symmetries carrying `x` to `y`. -/
def transporter (G : Type*) [Group G] {X : Type*} [MulAction G X] (x y : X) : Set G :=
  {g : G | g • x = y}

@[simp]
theorem mem_transporter {x y : X} {g : G} : g ∈ transporter G x y ↔ g • x = y := Iff.rfl

/-- If `h` carries `x` to `y`, then left translation by `h` is a bijection from the stabilizer
of `x` onto the transporter from `x` to `y`. -/
def stabilizerEquivTransporter {x y : X} (h : G) (hh : h • x = y) :
    stabilizer G x ≃ transporter G x y where
  toFun g := ⟨h * (g : G), by
    have : (g : G) • x = x := g.2
    simp [transporter, mul_smul, this, hh]⟩
  invFun g := ⟨h⁻¹ * (g : G), by
    have hg : (g : G) • x = y := g.2
    simp only [MulAction.mem_stabilizer_iff, mul_smul, hg, ← hh, inv_smul_smul]⟩
  left_inv g := by ext; simp
  right_inv g := by ext; simp

/-- All nonempty transporters have the same cardinality as the stabilizer. -/
theorem card_transporter_eq_card_stabilizer {x y : X} (h : G) (hh : h • x = y) :
    Nat.card (transporter G x y) = Nat.card (stabilizer G x) :=
  (Nat.card_congr (stabilizerEquivTransporter h hh)).symm

/-- Orbit-stabilizer theorem, in `Nat.card` form. -/
theorem card_orbit_mul_card_stabilizer (x : X) :
    Nat.card (orbit G x) * Nat.card (stabilizer G x) = Nat.card G := by
  rw [← Nat.card_prod]
  exact Nat.card_congr (orbitProdStabilizerEquivGroup G x)

theorem card_orbit_eq_card [IsPretransitive G X] (x : X) :
    Nat.card (orbit G x) = Nat.card X := by
  have : orbit G x = (Set.univ : Set X) := orbit_eq_univ G x
  rw [this]
  exact Nat.card_congr (Equiv.Set.univ X)

/-- **Equidistribution of a transitive symmetry group.**

If a group `G` acts transitively on `X`, then the symmetries are equidistributed over the
points of `X`: for any base point `x` and any target point `y`, the number of group elements
carrying `x` to `y` is exactly `Nat.card G / Nat.card X`, independently of `y`.  This is stated
in the division-free form `Nat.card X * Nat.card (transporter G x y) = Nat.card G`. -/
theorem equidistribution_of_transitive_symmetry [IsPretransitive G X] (x y : X) :
    Nat.card X * Nat.card (transporter G x y) = Nat.card G := by
  obtain ⟨h, hh⟩ := IsPretransitive.exists_smul_eq (M := G) x y
  rw [card_transporter_eq_card_stabilizer h hh, ← card_orbit_eq_card (G := G) x]
  exact card_orbit_mul_card_stabilizer x

/-- The equidistribution property, as a predicate on the action.  This is the named hypothesis
that is discharged below. -/
def IsEquidistributed (G : Type*) [Group G] (X : Type*) [MulAction G X] : Prop :=
  ∀ x y : X, Nat.card X * Nat.card (transporter G x y) = Nat.card G

/-- The equidistribution hypothesis holds unconditionally for any transitive action. -/
theorem isEquidistributed_of_isPretransitive [IsPretransitive G X] : IsEquidistributed G X :=
  fun x y => equidistribution_of_transitive_symmetry x y

/-- Uniformity: the transporters from a fixed base point to two different targets have equal
cardinality. -/
theorem card_transporter_eq_card_transporter [IsPretransitive G X] (x y z : X) :
    Nat.card (transporter G x y) = Nat.card (transporter G x z) := by
  obtain ⟨h, hh⟩ := IsPretransitive.exists_smul_eq (M := G) x y
  obtain ⟨k, hk⟩ := IsPretransitive.exists_smul_eq (M := G) x z
  rw [card_transporter_eq_card_stabilizer h hh, card_transporter_eq_card_stabilizer k hk]

/-- The order of a transitive symmetry group is divisible by the number of points. -/
theorem card_dvd_card_group [IsPretransitive G X] (x : X) :
    Nat.card X ∣ Nat.card G :=
  ⟨Nat.card (transporter G x x), (equidistribution_of_transitive_symmetry x x).symm⟩

/-- The explicit uniform count, for a finite group: every point receives exactly
`Nat.card G / Nat.card X` symmetries. -/
theorem card_transporter_eq_div [Finite G] [IsPretransitive G X] (x y : X) :
    Nat.card (transporter G x y) = Nat.card G / Nat.card X := by
  have hX : Nat.card X ≠ 0 := by
    have : Finite X := by
      have : Function.Surjective (fun g : G => g • x) := fun y =>
        IsPretransitive.exists_smul_eq (M := G) x y
      exact Finite.of_surjective _ this
    exact Nat.card_ne_zero.mpr ⟨⟨x⟩, this⟩
  rw [← equidistribution_of_transitive_symmetry (G := G) x y,
    Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hX)]

end EquidistributionUniformity
end Brockian

