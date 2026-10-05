/-
# Thurston Geometrization
Category: Frontier — Fields Medal Work
Target: Frontier.thurston_geometrization
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

/-! ## The eight Thurston model geometries -/

/-- The eight three-dimensional Thurston model geometries:
`E3` (Euclidean), `S3` (spherical), `H3` (hyperbolic), `S2xR`, `H2xR`,
`SL2R` (the universal cover of `SL(2,ℝ)`), `Nil` and `Sol`. -/
inductive Geometry
  | E3
  | S3
  | H3
  | S2xR
  | H2xR
  | SL2R
  | Nil
  | Sol
  deriving DecidableEq, Fintype, Repr

/-- There are exactly eight Thurston geometries. -/

theorem thurston_geometrization' (T : ThreeManifoldTheory) (m : T.Mfld) :
    ∃ l : List T.Mfld, m = T.connectedSum l ∧ ∀ p ∈ l, T.IsPrime p ∧ T.Geometrizable p :=
  thurston_geometrization T m

/-! ## Consistency of the interface

A concrete (toy) model of `ThreeManifoldTheory`, showing that the axioms
recorded in the interface are consistent, so that the theorems above are not
vacuous. -/

/-- A toy model: manifolds are natural numbers, connected sum is addition,
the sphere is `0`, and the unique prime is `1`, carrying the spherical
geometry. -/
