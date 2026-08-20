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

def AdmitsGeometricStructure (M : Type) [TopologicalSpace M] (X : ModelSpace) : Prop :=
  ∃ A : GeometricAction X, Nonempty (M ≃ₜ GeometricQuotient X A)

/-- A geometric quotient is compact: it is the continuous image of a compact set. -/
instance compactSpace_geometricQuotient (X : ModelSpace) (A : GeometricAction X) :
    CompactSpace (GeometricQuotient X A) := by
  obtain ⟨K, hK, hcov⟩ := A.cocompact
  constructor
  have himg : (Set.univ : Set (GeometricQuotient X A)) =
      (Quotient.mk (orbitSetoid X A.group)) '' K := by
    ext q
    refine ⟨fun _ => ?_, fun _ => trivial⟩
    induction q using Quotient.inductionOn with
    | h x =>
      obtain ⟨g, hg, hgx⟩ := hcov x
      exact ⟨g x, hgx, Quotient.sound ⟨g⁻¹, A.group.inv_mem hg, by simp⟩⟩
  rw [show (Set.univ : Set (GeometricQuotient X A)) = _ from himg]
  exact hK.image continuous_quotient_mk'

/-- A geometric quotient is connected: a model geometry is simply connected, hence connected. -/
instance connectedSpace_geometricQuotient (X : ModelSpace) (A : GeometricAction X) :
    ConnectedSpace (GeometricQuotient X A) :=
  inferInstanceAs (ConnectedSpace (Quotient (orbitSetoid X A.group)))

/-! ## Base case: the Euclidean model `E³` and the flat 3-torus -/

/-- Euclidean 3-space, the underlying space of the model geometry `E³`. -/
abbrev EuclideanThreeSpace : Type := EuclideanSpace ℝ (Fin 3)

/-- The model geometry `E³`. -/
