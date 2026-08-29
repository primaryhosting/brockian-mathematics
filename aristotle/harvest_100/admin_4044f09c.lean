/-!
# Equidistribution Of Transitive Symmetry
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionUniformity.equidistribution_of_transitive_symmetry
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian
namespace EquidistributionUniformity

/-- **Equidistribution of a transitive symmetry group.**

If a finite group `G` acts transitively on a finite type `X`, then pushing the uniform
distribution on `G` forward along the orbit map `g ↦ g • x` yields the uniform distribution
on `X`: every point `y : X` is hit by exactly `|G| / |X|` group elements, i.e. the fiber
`{g : G | g • x = y}` has cardinality `c` with `c * |X| = |G|`.

The statement is unconditional: no auxiliary hypothesis beyond transitivity of the action
and finiteness is assumed (in particular no nonemptiness hypothesis is needed, since the
identity `0 * 0 = 0` holds in the empty case as well). -/
theorem equidistribution_of_transitive_symmetry
    {G X : Type*} [Group G] [Fintype G] [MulAction G X] [Fintype X]
    [MulAction.IsPretransitive G X] (x y : X) :
    (Finset.univ.filter (fun g : G => g • x = y)).card * Fintype.card X = Fintype.card G := by
  obtain ⟨g₀, hg₀⟩ := MulAction.exists_smul_eq G x y
  -- The fiber over `y` is the left coset `g₀ • stabilizer G x`, hence has the size of the
  -- stabilizer.
  have hstab : (Finset.univ.filter (fun g : G => g • x = y)).card
      = Fintype.card (MulAction.stabilizer G x) := by
    rw [Fintype.card_subtype]
    refine Finset.card_bij' (fun g _ => g₀⁻¹ * g) (fun h _ => g₀ * h) ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      simp [MulAction.mem_stabilizer_iff, mul_smul, ha, ← hg₀, inv_smul_smul]
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        MulAction.mem_stabilizer_iff] at ha ⊢
      rw [mul_smul, ha, hg₀]
    · intro a _; group
    · intro a _; group
  -- Transitivity identifies the orbit of `x` with all of `X`; conclude by orbit–stabilizer.
  have horb : Fintype.card (MulAction.orbit G x) = Fintype.card X := by
    simp [MulAction.orbit_eq_univ G x]
  rw [hstab, ← horb, mul_comm]
  exact MulAction.card_orbit_mul_card_stabilizer_eq_card_group G x

/-- Uniformity restated: all fibers of the orbit map have the same cardinality. -/
theorem card_fiber_eq_of_transitive_symmetry
    {G X : Type*} [Group G] [Fintype G] [MulAction G X] [Fintype X]
    [MulAction.IsPretransitive G X] (x y z : X) :
    (Finset.univ.filter (fun g : G => g • x = y)).card
      = (Finset.univ.filter (fun g : G => g • x = z)).card := by
  have hy := equidistribution_of_transitive_symmetry (G := G) x y
  have hz := equidistribution_of_transitive_symmetry (G := G) x z
  have hX : 0 < Fintype.card X := Fintype.card_pos_iff.mpr ⟨x⟩
  exact Nat.eq_of_mul_eq_mul_right hX (hy.trans hz.symm)

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

