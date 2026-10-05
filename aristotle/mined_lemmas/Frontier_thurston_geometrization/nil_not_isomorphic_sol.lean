/-
# Thurston Geometrization
Category: Frontier — Fields Medal Work
Target: Frontier.thurston_geometrization
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- The eight three-dimensional Thurston model geometries:
Euclidean `E³`, spherical `S³`, hyperbolic `H³`, the two product geometries
`S² × ℝ` and `H² × ℝ`, the universal cover of `SL(2,ℝ)`, `Nil` (the Heisenberg
group) and `Sol`. -/
inductive Geometry
  | E3 | S3 | H3 | S2xR | H2xR | SL2R | Nil | Sol
  deriving DecidableEq, Repr, Fintype

namespace Geometry

/-- There are exactly eight Thurston geometries. -/

theorem nil_not_isomorphic_sol : IsEmpty (NilModel ≃* SolModel) := by
  constructor
  intro e
  obtain ⟨a, b, c, hab⟩ := SolModel.exists_commutator_not_central
  apply hab
  have key := NilModel.commutator_central (e.symm a) (e.symm b) (e.symm c)
  have := congrArg e key
  simpa using this

/-! ## An abstract framework for the geometrization theorem

We package the topological input of geometrization as data: a type of closed
oriented 3-manifolds (up to homeomorphism), the connected sum operation with
unit `S³`, primeness, and, for each manifold, the list of pieces obtained by
cutting along the JSJ tori together with the model geometry (if any) carried by
each piece. -/

/-- Abstract data describing closed oriented 3-manifolds, their prime and JSJ
decompositions, and the geometry carried by each JSJ piece. -/
structure ThreeManifoldData where
  /-- Closed oriented 3-manifolds up to homeomorphism. -/
  Closed : Type
  /-- Compact 3-manifolds with (possibly empty) toral boundary: the pieces. -/
  Piece : Type
  /-- Connected sum. -/
  connSum : Closed → Closed → Closed
  /-- The 3-sphere: the unit for connected sum. -/
  sphere : Closed
  /-- Primeness (no nontrivial connected sum decomposition). -/
  Prime : Closed → Prop
  /-- The pieces of the JSJ decomposition of a manifold. -/
  pieces : Closed → List Piece
  /-- The model geometry carried by the interior of a piece, when there is one. -/
  geometry : Piece → Option Geometry
  /-- A piece is Seifert fibred. -/
  SeifertFibered : Piece → Prop
  /-- A piece is a Sol-manifold (torus bundle or semibundle). -/
  SolType : Piece → Prop
  /-- A piece is atoroidal. -/
  Atoroidal : Piece → Prop

namespace ThreeManifoldData

variable (T : ThreeManifoldData)

/-- A piece is geometric if its interior admits one of the eight geometries. -/
