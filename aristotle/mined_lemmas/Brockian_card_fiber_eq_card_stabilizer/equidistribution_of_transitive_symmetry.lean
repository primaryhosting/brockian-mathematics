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
open scoped Pointwise

set_option maxHeartbeats 800000

namespace Brockian
namespace EquidistributionUniformity

/-- **Fibres of a transitive action are cosets of a stabiliser.**

If a group `G` acts transitively on `X` and `g₀ • x = y`, then the set of group elements
carrying `x` to `y` is in bijection with the stabiliser of `x`; in particular the fibres of
the orbit map `g ↦ g • x` all have the same cardinality. -/

theorem equidistribution_of_transitive_symmetry
    {G X : Type*} [Group G] [Fintype G] [MulAction G X] [Fintype X]
    [MulAction.IsPretransitive G X] (x y : X) :
    {g : G | g • x = y}.toFinset.card * Fintype.card X = Fintype.card G := by
  obtain ⟨g₀, hg₀⟩ := MulAction.exists_smul_eq G x y
  have hstab := card_fiber_eq_card_stabilizer x y g₀ hg₀
  have horb : Fintype.card ↥(MulAction.orbit G x) = Fintype.card X :=
    Fintype.card_congr ((Equiv.setCongr (MulAction.orbit_eq_univ G x)).trans (Equiv.Set.univ X))
  rw [hstab, ← horb, mul_comm]
  exact MulAction.card_orbit_mul_card_stabilizer_eq_card_group G x

/-- Consequence: the fibre counts of the orbit map are independent of the target point,
which is the equidistribution statement in its "all fibres have equal size" form. -/
