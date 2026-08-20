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

namespace Frontier

open Metric Module Set Topology

/-- The standard `3`-sphere, realized as the unit sphere of `ℝ⁴`. -/
abbrev Sphere3 : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

/-- The statement of the **Poincaré conjecture** (a theorem of Perelman): every simply
connected closed (= compact, without boundary) topological `3`-manifold is homeomorphic to
the `3`-sphere.

Being a closed `3`-manifold is encoded as: Hausdorff, compact, and locally modelled on
`ℝ³` (a `ChartedSpace (EuclideanSpace ℝ (Fin 3))` structure). Note that compactness together
with the charted space structure automatically gives second countability. -/

noncomputable def puncturedSphere3Homeo (v : Sphere3) :
    ({v}ᶜ : Set Sphere3) ≃ₜ EuclideanSpace ℝ (Fin 3) := by
  have hv : ‖(v : EuclideanSpace ℝ (Fin 4))‖ = 1 := by simp
  have hv0 : (v : EuclideanSpace ℝ (Fin 4)) ≠ 0 := by
    intro h; rw [h] at hv; simp at hv
  -- the punctured sphere is homeomorphic to the orthogonal complement of `v`
  have hrange : Set.range (stereographic hv).symm = ({v}ᶜ : Set Sphere3) := by
    rw [range_stereographic_symm hv (by simp)]
  let e₁ : ((ℝ ∙ (v : EuclideanSpace ℝ (Fin 4)))ᗮ) ≃ₜ ({v}ᶜ : Set Sphere3) :=
    ((isOpenEmbedding_stereographic_symm hv).isEmbedding.toHomeomorph).trans
      (Homeomorph.setCongr hrange)
  -- and that complement is a `3`-dimensional real inner product space
  have hfin : finrank ℝ (EuclideanSpace ℝ (Fin 3)) =
      finrank ℝ ((ℝ ∙ (v : EuclideanSpace ℝ (Fin 4)))ᗮ) := by
    haveI : Fact (finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩
    rw [Submodule.finrank_orthogonal_span_singleton (n := 3) hv0]
    simp
  let e₂ : EuclideanSpace ℝ (Fin 3) ≃ₜ ((ℝ ∙ (v : EuclideanSpace ℝ (Fin 4)))ᗮ) :=
    (FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq hfin).some
  exact (e₂.trans e₁).symm

/-- **Characterization of the `3`-sphere among compact Hausdorff spaces by a puncture.**
A compact Hausdorff space is homeomorphic to `S³` if and only if it has a point whose
complement is homeomorphic to `ℝ³`. -/
