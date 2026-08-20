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

theorem secondCountable_of_compact_manifold (n : ℕ) {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [CompactSpace M] :
    SecondCountableTopology M := by
  set E := EuclideanSpace ℝ (Fin n)
  have hcover : ⋃ x : M, (chartAt E x).source = Set.univ := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨y, mem_chart_source E y⟩
  obtain ⟨t, ht⟩ := IsCompact.elim_finite_subcover (isCompact_univ (X := M))
    (fun x : M => (chartAt E x).source) (fun x => (chartAt E x).open_source)
    (by rw [hcover])
  have hsc : ∀ x : M, SecondCountableTopology ((chartAt E x).source : Set M) :=
    fun x => (chartAt E x).toHomeomorphSourceTarget.secondCountableTopology
  have hcover2 : ⋃ x : {x : M // x ∈ t}, (chartAt E (x : M)).source = Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    intro y _
    have hy := ht (Set.mem_univ y)
    simp only [Set.mem_iUnion, exists_prop] at hy ⊢
    obtain ⟨x, hx, hyx⟩ := hy
    exact ⟨⟨x, hx⟩, hyx⟩
  exact @TopologicalSpace.secondCountableTopology_of_countable_cover M _ {x : M // x ∈ t} _
    (fun x => (chartAt E (x : M)).source) (fun x => hsc (x : M))
    (fun x => (chartAt E (x : M)).open_source) hcover2

/-- Every closed (compact Hausdorff) `n`-manifold is metrizable; in particular the spaces
occurring in the Poincaré conjecture are metrizable, second countable spaces. -/
