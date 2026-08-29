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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- The eight Thurston model geometries for closed `3`-manifolds:
`E³`, `S³`, `H³`, `S² × ℝ`, `H² × ℝ`, `SL(2,ℝ)~`, `Nil`, `Sol`. -/
inductive Geometry : Type
  | E3
  | S3
  | H3
  | S2xR
  | H2xR
  | SLtwoR
  | Nil
  | Sol
  deriving DecidableEq, Fintype, Repr

namespace Geometry

/-- There are exactly eight Thurston geometries. -/

def ToralGeometrizable (p : T.Mfld) : Prop :=
  ∃ ks : List T.Mfld, T.JSJ p ks ∧ ∀ k ∈ ks, T.IsGeometric k

/-- The full geometrization property of a manifold: it is a connected sum of prime
pieces, each of which is cut along incompressible tori into geometric pieces. -/
