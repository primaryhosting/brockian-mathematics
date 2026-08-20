/-
# Figalli OT Regularity
Category: Frontier — Fields Medal Work
Target: Frontier.figalli_OT_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The quadratic (Brenier) transport cost `c(x,y) = ‖x - y‖²/2`. -/

theorem inner_gradient_le_sub {Ω : Set E} {u : E → ℝ} (hu : ConvexOn ℝ Ω u)
    {y z : E} (hy : y ∈ Ω) (hz : z ∈ Ω) (hdy : DifferentiableAt ℝ u y) :
    ⟪gradient u y, z - y⟫_ℝ ≤ u z - u y := by
  set A : ℝ →ᵃ[ℝ] E := AffineMap.lineMap y z with hA
  have hA0 : (A : ℝ → E) 0 = y := by simp [hA]
  have hmaps : Set.Icc (0 : ℝ) 1 ⊆ (A : ℝ → E) ⁻¹' Ω := fun t ht => hu.1.lineMap_mem hy hz ht
  have hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (u ∘ (A : ℝ → E)) :=
    (hu.comp_affineMap A).subset hmaps (convex_Icc 0 1)
  have h1 : HasDerivAt (fun t : ℝ => (A : ℝ → E) t) (z - y) 0 := by
    simp only [hA, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (z - y)).add_const y
  have hderiv : HasDerivAt (u ∘ (A : ℝ → E)) (fderiv ℝ u y (z - y)) 0 := by
    have h2 : HasFDerivAt u (fderiv ℝ u y) ((A : ℝ → E) 0) := by rw [hA0]; exact hdy.hasFDerivAt
    exact h2.comp_hasDerivAt 0 h1
  have key := hconv.le_slope_of_hasDerivWithinAt (x := 0) (y := 1) (by simp) (by simp)
    (by norm_num) hderiv.hasDerivWithinAt
  have hslope : slope (u ∘ (A : ℝ → E)) 0 1 = u z - u y := by simp [slope_def_field, hA]
  rw [hslope] at key
  rw [inner_gradient_left hdy]
  exact key

/-- **Optimality of the Brenier map.** The graph of the gradient of a convex function is
`c`-cyclically monotone for the quadratic cost; hence `∇u` is an optimal transport map
between any two measures that it couples. -/
