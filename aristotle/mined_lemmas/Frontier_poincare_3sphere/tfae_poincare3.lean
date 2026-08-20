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

theorem tfae_poincare3 :
    List.TFAE [Poincare3Conjecture.{u}, Poincare3Bij.{u}, Poincare3Rev.{u}, Poincare3Emb.{u},
      Poincare3Pi1.{u}] := by
  have key : ∀ (M : Type u) [TopologicalSpace M] [T2Space M] [CompactSpace M],
      List.TFAE
        [Nonempty (M ≃ₜ Sphere3),
         ∃ f : M → Sphere3, Continuous f ∧ Function.Bijective f,
         ∃ g : Sphere3 → M, Continuous g ∧ Function.Bijective g,
         ∃ f : M → Sphere3, IsEmbedding f ∧ Function.Surjective f] := by
    intro M _ _ _
    exact tfae_homeomorph_of_compact_t2 M Sphere3
  tfae_have 1 → 2 := by
    intro h M _ _ _ _ _
    exact ((key M).out 0 1).1 (h M)
  tfae_have 2 → 1 := by
    intro h M _ _ _ _ _
    exact ((key M).out 0 1).2 (h M)
  tfae_have 1 → 3 := by
    intro h M _ _ _ _ _
    exact ((key M).out 0 2).1 (h M)
  tfae_have 3 → 1 := by
    intro h M _ _ _ _ _
    exact ((key M).out 0 2).2 (h M)
  tfae_have 1 → 4 := by
    intro h M _ _ _ _ _
    exact ((key M).out 0 3).1 (h M)
  tfae_have 4 → 1 := by
    intro h M _ _ _ _ _
    exact ((key M).out 0 3).2 (h M)
  tfae_have 1 ↔ 5 := poincare3_pi1_iff
  tfae_finish

/-!
## The reduction using invariance of domain
-/

/-- Modulo invariance of domain, a continuous injection between `n`-manifolds is an open map. -/
