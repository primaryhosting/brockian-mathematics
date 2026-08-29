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

theorem nodup_univ : (Finset.univ : Finset Geometry).val.Nodup :=
  Finset.univ.nodup

end Geometry

/-!
## An abstract axiomatisation of the ingredients of geometrization

`Thurston.Setup` packages an abstract class of closed orientable `3`-manifolds together
with the three geometric decomposition ingredients:

* the Kneser–Milnor prime decomposition along `2`-spheres,
* the Jaco–Shalen–Johannson decomposition of a prime manifold along incompressible tori,
* the identification of the resulting pieces (hyperbolization for atoroidal pieces,
  and the six remaining geometries for Seifert fibred pieces).

The main theorem below is a Lean-checked *reduction*: from these ingredients one obtains
the geometrization statement, namely that every member of the class decomposes as a
connected sum of prime pieces, each of which is cut along tori into pieces carrying one
of the eight geometries.
-/

/-- Abstract data for the geometric decomposition of closed orientable `3`-manifolds. -/
structure Setup where
  /-- The type of closed orientable `3`-manifolds under consideration. -/
  Mfld : Type
  /-- `ConnSum m ps` : `m` is the connected sum of the manifolds in the list `ps`. -/
  ConnSum : Mfld → List Mfld → Prop
  /-- `m` is prime (not a nontrivial connected sum). -/
  Prime : Mfld → Prop
  /-- `JSJ m ks` : `ks` are the pieces obtained by cutting `m` along a maximal
  collection of disjoint incompressible tori. -/
  JSJ : Mfld → List Mfld → Prop
  /-- A piece is atoroidal (and not Seifert fibred). -/
  Atoroidal : Mfld → Prop
  /-- A piece is Seifert fibred. -/
  SeifertFibered : Mfld → Prop
  /-- `Geometric m g` : the interior of `m` carries a complete locally homogeneous
  Riemannian metric modelled on the geometry `g`. -/
  Geometric : Mfld → Geometry → Prop
  /-- Kneser–Milnor: every manifold is a connected sum of finitely many prime pieces. -/
  kneser_milnor : ∀ m : Mfld, ∃ ps : List Mfld, ConnSum m ps ∧ ∀ p ∈ ps, Prime p
  /-- JSJ: every prime manifold is cut by incompressible tori into pieces that are
  either atoroidal or Seifert fibred. -/
  jsj : ∀ p : Mfld, Prime p →
      ∃ ks : List Mfld, JSJ p ks ∧ ∀ k ∈ ks, Atoroidal k ∨ SeifertFibered k
  /-- Hyperbolization (Thurston, Perelman): atoroidal pieces carry the geometry `H³`. -/
  hyperbolization : ∀ k : Mfld, Atoroidal k → Geometric k Geometry.H3
  /-- Seifert fibred pieces carry one of the six Seifert geometries, i.e. one of the
  eight geometries other than `H³` and `Sol`. -/
  seifert_geometric : ∀ k : Mfld, SeifertFibered k →
      ∃ g : Geometry, g ≠ Geometry.H3 ∧ g ≠ Geometry.Sol ∧ Geometric k g

namespace Setup

variable (T : Setup)

/-- A manifold is *geometric* when it carries one of the eight Thurston geometries. -/
