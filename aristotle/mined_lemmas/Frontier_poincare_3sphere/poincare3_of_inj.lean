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

theorem poincare3_of_inj (hIoD : InvarianceOfDomain 3) (h : Poincare3Inj.{u}) :
    Poincare3Conjecture.{u} := by
  intro M _ _ _ _ _
  obtain ⟨f, hf, hinj⟩ := h M
  exact homeomorph_of_continuous_injective 3 hIoD f hf hinj

/-!
## Main statement
-/

/-- **The Poincaré conjecture in dimension 3: formalized statement together with Lean-checked
reductions.**

`Poincare3Conjecture` is the statement that every simply connected closed (compact, boundaryless)
topological 3-manifold is homeomorphic to `S³`.

The first component below is an unconditional equivalence of the conjecture with four
reformulations: it suffices to produce a continuous bijection to `S³`, or a continuous bijection
from `S³`, or a surjective topological embedding into `S³`; and the hypothesis "simply connected"
may equivalently be spelled out as "path connected with trivial fundamental group".

The second component is a reduction of the full conjecture to the *a priori* weaker statement
`Poincare3Inj`, that every simply connected closed 3-manifold admits a continuous injection into
`S³`; this reduction is proved modulo Brouwer's invariance of domain, which is supplied as an
explicit hypothesis since it is not available in Mathlib. -/
