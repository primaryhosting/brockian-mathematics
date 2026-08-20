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

theorem homeomorph_of_isOpenMap_injective {M : Type u} [TopologicalSpace M] [CompactSpace M]
    [Nonempty M] {N : Type v} [TopologicalSpace N] [T2Space N] [ConnectedSpace N]
    (f : M → N) (hf : Continuous f) (hinj : Function.Injective f) (hopen : IsOpenMap f) :
    Nonempty (M ≃ₜ N) := by
  have hsurj : Function.Surjective f := by
    have hclopen : IsClopen (Set.range f) :=
      ⟨(isCompact_range hf).isClosed, hopen.isOpen_range⟩
    rcases isClopen_iff.1 hclopen with h | h
    · exact absurd h (by simp [Set.eq_empty_iff_forall_notMem])
    · intro y
      have : y ∈ Set.range f := h ▸ Set.mem_univ y
      exact this
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f ⟨hinj, hsurj⟩) hf⟩

/-- Modulo invariance of domain: a continuous injection from a nonempty compact `n`-manifold
into a connected Hausdorff `n`-manifold is a homeomorphism. -/
