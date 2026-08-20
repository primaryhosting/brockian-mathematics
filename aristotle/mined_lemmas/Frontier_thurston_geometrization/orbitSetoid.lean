import Mathlib

/-!
# Thurston Geometrization
Category: Frontier — Fields Medal Work
Target: Frontier.thurston_geometrization
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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-! ## The eight Thurston geometries -/

/-- The eight three-dimensional Thurston model geometries. -/
inductive ThurstonGeometry
  /-- Euclidean space `E³`. -/
  | euclidean
  /-- The round sphere `S³`. -/
  | spherical
  /-- Hyperbolic space `H³`. -/
  | hyperbolic
  /-- The product geometry `S² × ℝ`. -/
  | sphereTimesLine
  /-- The product geometry `H² × ℝ`. -/
  | hyperbolicPlaneTimesLine
  /-- The universal cover of `SL(2,ℝ)`. -/
  | slTwoTilde
  /-- Nil geometry (the Heisenberg group). -/
  | nil
  /-- Sol geometry. -/
  | sol
  deriving DecidableEq, Fintype, Repr

/-- There are exactly eight Thurston geometries. -/

def orbitSetoid (X : ModelSpace) (Γ : Subgroup (X.carrier ≃ᵢ X.carrier)) :
    Setoid X.carrier where
  r x y := ∃ g ∈ Γ, g x = y
  iseqv := by
    refine ⟨fun x => ⟨1, Γ.one_mem, rfl⟩, ?_, ?_⟩
    · rintro x y ⟨g, hg, rfl⟩
      exact ⟨g⁻¹, Γ.inv_mem hg, by simp⟩
    · rintro x y z ⟨g, hg, rfl⟩ ⟨h, hh, rfl⟩
      exact ⟨h * g, Γ.mul_mem hh hg, rfl⟩

/-- The quotient of a model space by a geometric action: a closed geometric manifold. -/
