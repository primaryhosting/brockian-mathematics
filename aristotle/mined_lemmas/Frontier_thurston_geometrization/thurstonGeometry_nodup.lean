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

theorem thurstonGeometry_nodup :
    (Finset.univ : Finset ThurstonGeometry) =
      {ThurstonGeometry.E3, ThurstonGeometry.S3, ThurstonGeometry.H3, ThurstonGeometry.S2xR,
        ThurstonGeometry.H2xR, ThurstonGeometry.SL2R, ThurstonGeometry.Nil,
        ThurstonGeometry.Sol} := by
  decide

/-! ## An abstract axiomatisation of closed 3-manifold topology

Formalising smooth 3-manifolds, connected sums, incompressible tori and locally homogeneous
Riemannian metrics inside Mathlib is far beyond what is currently available, so we work with an
abstract *interface*: a type of (closed, oriented) 3-manifolds together with the predicates that
occur in the statement of the Geometrization Theorem.  All the deep geometric input
(Kneser–Milnor, Jaco–Shalen–Johannson, Thurston–Perelman) enters only as hypotheses, and what we
prove is the *reduction*: those three inputs together imply the full geometric decomposition
statement. -/

/-- An abstract interface for the topology of closed oriented 3-manifolds.

* `Mfld` is the type of manifolds (thought of as diffeomorphism classes);
* `IsClosedOriented M` says `M` is a closed oriented 3-manifold;
* `Geometric M G` says `M` admits a complete locally homogeneous Riemannian metric modelled on
  the Thurston geometry `G`;
* `ConnectedSumDecomp M ps` says `M` is the connected sum of the manifolds in the list `ps`;
* `IsPrime M` says `M` is prime (not a nontrivial connected sum);
* `TorusDecomp M qs` says cutting `M` along a finite family of disjoint embedded incompressible
  tori yields exactly the pieces `qs`;
* `IsSeifertOrAtoroidal M` says the piece `M` is Seifert fibred or atoroidal, i.e. it is a JSJ
  piece. -/
structure ThreeManifoldTheory where
  /-- The type of 3-manifolds. -/
  Mfld : Type
  /-- Being a closed oriented 3-manifold. -/
  IsClosedOriented : Mfld → Prop
  /-- Admitting a geometric structure modelled on a given Thurston geometry. -/
  Geometric : Mfld → ThurstonGeometry → Prop
  /-- Being the connected sum of a list of manifolds. -/
  ConnectedSumDecomp : Mfld → List Mfld → Prop
  /-- Being prime. -/
  IsPrime : Mfld → Prop
  /-- Being cut along incompressible tori into a list of pieces. -/
  TorusDecomp : Mfld → List Mfld → Prop
  /-- Being a JSJ piece: Seifert fibred or atoroidal. -/
  IsSeifertOrAtoroidal : Mfld → Prop

namespace ThreeManifoldTheory

variable (T : ThreeManifoldTheory)

/-- `M` is *geometric*: it carries a structure modelled on one of the eight geometries. -/
