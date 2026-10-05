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

theorem euclideanSpace3_commutative (p q : EuclideanSpace3) : p + q = q + p :=
  add_comm p q

/-!
## 3. An abstract framework for closed three–manifolds

Formalizing smooth three–manifolds, connected sums, incompressible tori and
locally homogeneous Riemannian metrics from scratch is far beyond what is
available in Mathlib.  Instead we axiomatize the *combinatorial shape* of the
geometrization theorem: a `ThreeManifoldTheory` records

* a type `Mfld` of (diffeomorphism classes of) closed oriented 3–manifolds,
* the connected sum operation with unit the 3–sphere,
* the predicate `IsPrime` of prime manifolds,
* a type `Piece` of compact pieces with (possibly empty) torus boundary,
* the relation `IsJSJ m ps` — "`ps` is the list of pieces obtained by cutting
  `m` along its JSJ tori",
* the relation `AdmitsGeometry p g` — "the piece `p` carries a complete locally
  homogeneous metric modelled on the geometry `g`".

All statements below are theorems *about* such a structure: they carry the
geometric input as explicit hypotheses and derive the global statement from it.
-/

/-- Abstract data for a theory of closed oriented three–manifolds. -/
structure ThreeManifoldTheory where
  /-- Diffeomorphism classes of closed oriented 3–manifolds. -/
  Mfld : Type
  /-- Connected sum. -/
  connSum : Mfld → Mfld → Mfld
  /-- The 3–sphere, the unit for connected sum. -/
  sphere3 : Mfld
  /-- Being a prime manifold. -/
  IsPrime : Mfld → Prop
  /-- Compact pieces with torus boundary arising from the JSJ decomposition. -/
  Piece : Type
  /-- `IsJSJ m ps` : cutting `m` along its JSJ tori yields the pieces `ps`. -/
  IsJSJ : Mfld → List Piece → Prop
  /-- `AdmitsGeometry p g` : the piece `p` carries a geometry modelled on `g`. -/
  AdmitsGeometry : Piece → Geometry → Prop

namespace ThreeManifoldTheory

variable (T : ThreeManifoldTheory)

/-- `m` is *geometrizable*: cutting it along spheres and tori yields pieces each
of which carries one of the eight Thurston geometries. -/
