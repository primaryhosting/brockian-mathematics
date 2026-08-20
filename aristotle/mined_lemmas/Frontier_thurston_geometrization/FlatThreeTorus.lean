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

noncomputable def FlatThreeTorus : Type := GeometricQuotient euclideanModel flatTorusAction

noncomputable instance : TopologicalSpace FlatThreeTorus :=
  inferInstanceAs (TopologicalSpace (GeometricQuotient euclideanModel flatTorusAction))

instance : CompactSpace FlatThreeTorus :=
  inferInstanceAs (CompactSpace (GeometricQuotient euclideanModel flatTorusAction))

instance : ConnectedSpace FlatThreeTorus :=
  inferInstanceAs (ConnectedSpace (GeometricQuotient euclideanModel flatTorusAction))

/-- The flat 3-torus is not a point: the classes of `0` and of the half-lattice vector differ. -/
instance : Nontrivial FlatThreeTorus := by
  refine ⟨⟨Quotient.mk (orbitSetoid euclideanModel flatTorusAction.group)
      (0 : EuclideanThreeSpace),
    Quotient.mk (orbitSetoid euclideanModel flatTorusAction.group)
      (WithLp.toLp 2 (fun i : Fin 3 => if i = 0 then (1 / 2 : ℝ) else 0)), ?_⟩⟩
  intro hcontra
  obtain ⟨g, hg, hgx⟩ := Quotient.exact hcontra
  obtain ⟨v, rfl⟩ := hg
  have h0 : (transl (intVec v) (0 : EuclideanThreeSpace)) 0 =
      (WithLp.toLp 2 (fun i : Fin 3 => if i = 0 then (1 / 2 : ℝ) else 0)) 0 := by
    exact congrArg (fun y : EuclideanThreeSpace => y 0) hgx
  simp only [transl_apply, zero_add, intVec_apply] at h0
  norm_num at h0
  have h1 : (2 * v 0 : ℤ) = 1 := by exact_mod_cast (by linarith : (2 * (v 0 : ℝ)) = 1)
  omega

/-- **Base case of geometrization.** The flat 3-torus is a closed manifold carrying the
Euclidean geometry `E³`. -/
