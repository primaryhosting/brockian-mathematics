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

theorem connectedSum_append (l₁ l₂ : List T.Mfld) :
    T.connectedSum (l₁ ++ l₂) = T.csum (T.connectedSum l₁) (T.connectedSum l₂) := by
  induction l₁ with
  | nil => simp [T.sphere_csum]
  | cons a l ih => simp [ih, T.csum_assoc]

/-- `m` is *geometrizable* if it splits along a system of incompressible tori
into pieces each of which carries one of the eight Thurston geometries. -/
