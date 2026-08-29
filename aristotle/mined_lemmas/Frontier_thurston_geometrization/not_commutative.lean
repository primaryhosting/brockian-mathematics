-- (Lean 4 requires `import` to be the very first command in a file, so the
-- module docstring header below follows the import.)
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

/-!
## 1. The eight Thurston geometries

Thurston's list of the eight maximal, simply connected, three–dimensional model
geometries admitting a compact quotient:

`E³`, `S³`, `H³`, `S² × ℝ`, `H² × ℝ`, `SL(2,ℝ)~`, `Nil`, `Sol`.
-/

/-- The eight three–dimensional Thurston model geometries. -/
inductive Geometry where
  /-- Euclidean geometry `E³`. -/
  | euclidean : Geometry
  /-- Spherical geometry `S³`. -/
  | spherical : Geometry
  /-- Hyperbolic geometry `H³`. -/
  | hyperbolic : Geometry
  /-- The product geometry `S² × ℝ`. -/
  | sphereTimesLine : Geometry
  /-- The product geometry `H² × ℝ`. -/
  | hyperbolicTimesLine : Geometry
  /-- The geometry of the universal cover of `SL(2,ℝ)`. -/
  | slTwoRCover : Geometry
  /-- Nil geometry (the Heisenberg group). -/
  | nil : Geometry
  /-- Sol geometry (the three-dimensional solvable Lie group). -/
  | sol : Geometry
  deriving DecidableEq, Fintype, Repr

/-- There are exactly eight Thurston geometries. -/

theorem not_commutative : ¬ ∀ p q : SolSpace, p * q = q * p := by
  intro h
  have hx := congrArg SolSpace.x (h ⟨0, 0, 1⟩ ⟨1, 0, 0⟩)
  simp at hx

/-- The subgroup `{t = 0}` of Sol is abelian: Sol is solvable. -/
