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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types false
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-! ## The eight Thurston geometries -/

/-- The eight three-dimensional Thurston model geometries:
Euclidean `E³`, spherical `S³`, hyperbolic `H³`, the two product geometries
`S² × ℝ` and `H² × ℝ`, the universal cover `SL₂(ℝ)~` of `SL₂(ℝ)`, `Nil` (the Heisenberg
group) and `Sol`. -/
inductive ThurstonGeometry : Type
  | E3 : ThurstonGeometry
  | S3 : ThurstonGeometry
  | H3 : ThurstonGeometry
  | S2xR : ThurstonGeometry
  | H2xR : ThurstonGeometry
  | SL2R : ThurstonGeometry
  | Nil : ThurstonGeometry
  | Sol : ThurstonGeometry
  deriving DecidableEq, Fintype, Repr

/-- There are exactly eight Thurston geometries. -/

def PrimeDecompositionAxiom : Prop :=
  ∀ M : T.Mfld, T.IsClosedOriented M →
    ∃ ps : List T.Mfld, T.ConnectedSumDecomp M ps ∧
      ∀ p ∈ ps, T.IsClosedOriented p ∧ T.IsPrime p

/-- Jaco–Shalen–Johannson torus decomposition: every prime closed oriented 3-manifold can be cut
along finitely many disjoint incompressible tori into Seifert fibred or atoroidal pieces. -/
