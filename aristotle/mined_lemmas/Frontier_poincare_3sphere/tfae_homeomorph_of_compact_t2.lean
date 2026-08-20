-- (Lean requires `import` lines to precede any module documentation, so the requested
-- header comment appears immediately below the import.)
import Mathlib

/-!
# Poincare 3 Sphere
Category: Frontier — Moonshot
Target: Frontier.poincare_3sphere
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

open Function Topology Metric

universe u v

/-- The model space `ℝ³`. -/
abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

/-- The 3-sphere `S³`, realized as the unit sphere in `ℝ⁴`. -/
abbrev Sphere3 : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

/-!
## `S³` is a closed connected 3-manifold

Mathlib already provides the instances `T2Space Sphere3`, `CompactSpace Sphere3` and
`ChartedSpace E3 Sphere3` (the stereographic atlas); we add connectedness.
-/

/-- The 3-sphere is connected. -/
instance sphere3_connectedSpace : ConnectedSpace Sphere3 := by
  have hrank : (1 : Cardinal) < Module.rank ℝ (EuclideanSpace ℝ (Fin 4)) := by
    rw [rank_eq_card_basis (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis]
    simp
  exact isConnected_iff_connectedSpace.1
    (isConnected_sphere hrank (0 : EuclideanSpace ℝ (Fin 4)) zero_le_one)

/-- The 3-sphere is path connected. -/
instance sphere3_pathConnectedSpace : PathConnectedSpace Sphere3 := by
  have hrank : (1 : Cardinal) < Module.rank ℝ (EuclideanSpace ℝ (Fin 4)) := by
    rw [rank_eq_card_basis (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis]
    simp
  exact isPathConnected_iff_pathConnectedSpace.1
    (isPathConnected_sphere hrank (0 : EuclideanSpace ℝ (Fin 4)) zero_le_one)

/-- `S³` is a compact Hausdorff, connected, three-dimensional charted space: i.e. a closed
connected topological 3-manifold. -/

theorem tfae_homeomorph_of_compact_t2 (M : Type u) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    (S : Type v) [TopologicalSpace S] [T2Space S] [CompactSpace S] :
    List.TFAE
      [Nonempty (M ≃ₜ S),
       ∃ f : M → S, Continuous f ∧ Function.Bijective f,
       ∃ g : S → M, Continuous g ∧ Function.Bijective g,
       ∃ f : M → S, IsEmbedding f ∧ Function.Surjective f] := by
  tfae_have 1 → 2 := by
    rintro ⟨e⟩; exact ⟨e, e.continuous, e.bijective⟩
  tfae_have 2 → 1 := by
    rintro ⟨f, hf, hbij⟩
    exact ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hbij) hf⟩
  tfae_have 1 → 3 := by
    rintro ⟨e⟩; exact ⟨e.symm, e.symm.continuous, e.symm.bijective⟩
  tfae_have 3 → 1 := by
    rintro ⟨g, hg, hbij⟩
    exact ⟨(Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g hbij) hg).symm⟩
  tfae_have 1 → 4 := by
    rintro ⟨e⟩; exact ⟨e, e.isEmbedding, e.surjective⟩
  tfae_have 4 → 2 := by
    rintro ⟨f, hemb, hsurj⟩
    exact ⟨f, hemb.continuous, hemb.injective, hsurj⟩
  tfae_finish

/-- The Poincaré conjecture is equivalent to each of its three reformulations. -/
