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

theorem card_fiber_eq_card_stabilizer
    {G X : Type*} [Group G] [Fintype G] [MulAction G X]
    (x y : X) (g₀ : G) (hg₀ : g₀ • x = y) :
    {g : G | g • x = y}.toFinset.card = Fintype.card ↥(MulAction.stabilizer G x) := by
  have hset : {g : G | g • x = y}.toFinset
      = Finset.univ.filter (fun g : G => g • x = y) := by
    ext g; simp
  rw [hset, Fintype.card_subtype]
  refine Finset.card_bij' (fun g _ => g₀⁻¹ * g) (fun h _ => g₀ * h) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    simp [MulAction.mem_stabilizer_iff, mul_smul, ha, ← hg₀]
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    rw [mul_smul, MulAction.mem_stabilizer_iff.mp hb, hg₀]
  · intro a _; simp
  · intro b _; simp

/-- **Equidistribution of a transitive symmetry group.**

Let a finite group `G` act transitively on a finite set `X`. Then the orbit map
`g ↦ g • x` distributes the group uniformly over `X`: for every target point `y`, the number
of symmetries carrying `x` to `y` is exactly `|G| / |X|`, stated multiplicatively as

`#{g : G | g • x = y} * |X| = |G|`.

In particular the count is independent of `y`, i.e. the uniform distribution on `G`
pushes forward to the uniform distribution on `X`. -/
