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

theorem flatThreeTorus_admits_euclidean :
    AdmitsGeometricStructure FlatThreeTorus euclideanModel :=
  ⟨flatTorusAction, ⟨Homeomorph.refl _⟩⟩

/-! ## The geometrization statement -/

/-- The topological input to geometrization: an abstract theory of closed oriented
3-manifolds, equipped with the prime (connected sum) decomposition, the JSJ (torus)
decomposition, and the geometrization of the resulting pieces. -/
structure ThreeManifoldTheory where
  /-- Closed oriented 3-manifolds, up to diffeomorphism. -/
  Mfd : Type
  /-- The underlying topological space of a manifold. -/
  space : Mfd → Type
  /-- The topology on the underlying space. -/
  topology : ∀ M, TopologicalSpace (space M)
  /-- The eight model geometries. -/
  models : ThurstonGeometry → ModelSpace
  /-- Primeness (irreducible, or `S² × S¹`). -/
  IsPrime : Mfd → Prop
  /-- `ConnectedSum M L` : `M` is the connected sum of the manifolds in `L`. -/
  ConnectedSum : Mfd → List Mfd → Prop
  /-- `JSJ N P` : cutting `N` along a canonical family of incompressible tori yields
  the pieces `P`. -/
  JSJ : Mfd → List Mfd → Prop
  /-- Being atoroidal (no essential embedded torus). -/
  IsAtoroidal : Mfd → Prop
  /-- Admitting a Seifert fibration. -/
  IsSeifertFibered : Mfd → Prop
  /-- Kneser–Milnor prime decomposition. -/
  prime_decomposition : ∀ M, ∃ L, ConnectedSum M L ∧ ∀ N ∈ L, IsPrime N
  /-- Jaco–Shalen–Johannson torus decomposition. -/
  jsj_decomposition : ∀ N, IsPrime N → ∃ P, JSJ N P
  /-- Each JSJ piece is either atoroidal or Seifert fibered. -/
  jsj_pieces_atoroidal_or_seifert : ∀ N P, IsPrime N → JSJ N P → ∀ p ∈ P,
    IsAtoroidal p ∨ IsSeifertFibered p
  /-- Hyperbolization: an atoroidal piece carries the geometry `H³`. -/
  hyperbolization : ∀ p, IsAtoroidal p →
    @AdmitsGeometricStructure (space p) (topology p) (models ThurstonGeometry.hyperbolic)
  /-- A Seifert fibered piece carries one of the six Seifert geometries, i.e. one of the eight
  geometries other than `H³` and `Sol`. -/
  seifert_geometrization : ∀ p, IsSeifertFibered p → ∃ g : ThurstonGeometry,
    g ≠ ThurstonGeometry.hyperbolic ∧ g ≠ ThurstonGeometry.sol ∧
      @AdmitsGeometricStructure (space p) (topology p) (models g)

/-- **Thurston's geometrization conjecture (Perelman's theorem), stated as a
Lean-checked reduction.**

Given a theory of closed oriented 3-manifolds satisfying the Kneser–Milnor prime
decomposition, the JSJ torus decomposition, the dichotomy "atoroidal or Seifert fibered"
for the JSJ pieces, Thurston's hyperbolization for the atoroidal pieces and geometrization
of Seifert fibered pieces, every closed oriented 3-manifold `M` decomposes as a connected
sum of prime manifolds, each of which is cut along tori into pieces, and every resulting
piece is the quotient of one of the eight Thurston model geometries by a free, properly
discontinuous, cocompact group of isometries; the atoroidal pieces are hyperbolic. -/
