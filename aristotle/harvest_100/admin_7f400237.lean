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

namespace Brockian.EquidistributionUniformity

variable (G : Type*) {X : Type*} [Group G] [MulAction G X]

/-- The fiber over `x` of the orbit map `g ↦ g • z`, as a `Finset` of group elements. -/
def transitionFinset [Fintype G] [DecidableEq X] (z x : X) : Finset G :=
  Finset.univ.filter fun g : G => g • z = x

/-- Every nonempty fiber of the orbit map `g ↦ g • z` is a left coset of the stabilizer of `z`,
hence has exactly `|stabilizer G z|` elements. -/
theorem card_transitionFinset_eq_card_stabilizer [Fintype G] [DecidableEq X]
    (z x : X) (g₀ : G) (hg₀ : g₀ • z = x) :
    (transitionFinset G z x).card = Nat.card (MulAction.stabilizer G z) := by
  classical
  have hcard : (transitionFinset G z x).card = Fintype.card {g : G // g • z = x} := by
    simp [transitionFinset, Fintype.card_subtype]
  rw [hcard, Nat.card_eq_fintype_card]
  refine Fintype.card_congr ?_
  refine
    { toFun := fun g => ⟨g₀⁻¹ * g.1, ?_⟩
      invFun := fun h => ⟨g₀ * h.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hg : g.1 • z = x := g.2
    have : (g₀⁻¹ * g.1) • z = g₀⁻¹ • (g.1 • z) := mul_smul _ _ _
    simp only [MulAction.mem_stabilizer_iff, this, hg, ← hg₀, inv_smul_smul]
  · have hz : h.1 • z = z := h.2
    rw [mul_smul, hz, hg₀]
  · intro g; ext; simp
  · intro h; ext; simp

/-- **Equidistribution of a transitive symmetry group.**

If a finite group `G` acts transitively on a finite type `X`, then the orbit map `g ↦ g • z`
distributes the elements of `G` uniformly over `X`: every point `x : X` is hit by exactly
`|G| / |X|` group elements, i.e. `|{g | g • z = x}| * |X| = |G|`.

The proof is the orbit–stabilizer theorem
(`MulAction.card_orbit_mul_card_stabilizer_eq_card_group`) combined with
`MulAction.orbit_eq_univ` for a pretransitive action; no extra uniformity hypothesis
is needed. -/
theorem equidistribution_of_transitive_symmetry [Fintype G] [Fintype X] [DecidableEq X]
    [MulAction.IsPretransitive G X] (z x : X) :
    (transitionFinset G z x).card * Fintype.card X = Fintype.card G := by
  classical
  obtain ⟨g₀, hg₀⟩ := MulAction.exists_smul_eq G z x
  have hfib := card_transitionFinset_eq_card_stabilizer G z x g₀ hg₀
  have horb : Fintype.card (MulAction.orbit G z) = Fintype.card X := by
    rw [Fintype.card_congr (Equiv.setCongr (MulAction.orbit_eq_univ G z))]
    exact Fintype.card_congr (Equiv.Set.univ X)
  have hos :
      Fintype.card (MulAction.orbit G z) * Fintype.card (MulAction.stabilizer G z)
        = Fintype.card G :=
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group G z
  rw [hfib, Nat.card_eq_fintype_card, mul_comm, ← horb, hos]

/-- All fibers of the orbit map of a transitive action have the same cardinality. -/
theorem card_transitionFinset_eq_card_transitionFinset [Fintype G] [Fintype X] [DecidableEq X]
    [MulAction.IsPretransitive G X] (z x y : X) :
    (transitionFinset G z x).card = (transitionFinset G z y).card := by
  have hx := equidistribution_of_transitive_symmetry G z x
  have hy := equidistribution_of_transitive_symmetry G z y
  have hX : 0 < Fintype.card X := Fintype.card_pos_iff.mpr ⟨x⟩
  exact Nat.eq_of_mul_eq_mul_right hX (hx.trans hy.symm)

end Brockian.EquidistributionUniformity

