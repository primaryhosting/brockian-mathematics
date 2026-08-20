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
