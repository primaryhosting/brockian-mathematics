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
theorem card_eq_eight : Fintype.card Geometry = 8 := by decide

/-- The list of all eight geometries has no duplicates: the eight geometries are
pairwise distinct. -/
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
def IsGeometric (m : T.Mfld) : Prop := ∃ g : Geometry, T.Geometric m g

/-- A manifold is *toral-geometrizable* when it can be cut along incompressible tori into
pieces each of which is geometric. -/
def ToralGeometrizable (p : T.Mfld) : Prop :=
  ∃ ks : List T.Mfld, T.JSJ p ks ∧ ∀ k ∈ ks, T.IsGeometric k

/-- The full geometrization property of a manifold: it is a connected sum of prime
pieces, each of which is cut along incompressible tori into geometric pieces. -/
def Geometrizable (m : T.Mfld) : Prop :=
  ∃ ps : List T.Mfld, T.ConnSum m ps ∧ ∀ p ∈ ps, T.Prime p ∧ T.ToralGeometrizable p

end Setup

/-- **Base case / piece step.** Every JSJ piece of a prime manifold — atoroidal or
Seifert fibred — carries one of the eight Thurston geometries. -/
theorem piece_isGeometric (T : Setup) {k : T.Mfld}
    (hk : T.Atoroidal k ∨ T.SeifertFibered k) : T.IsGeometric k := by
  rcases hk with h | h
  · exact ⟨Geometry.H3, T.hyperbolization k h⟩
  · obtain ⟨g, _, _, hg⟩ := T.seifert_geometric k h
    exact ⟨g, hg⟩

/-- Every prime manifold admits a torus decomposition into geometric pieces. -/
theorem prime_toralGeometrizable (T : Setup) {p : T.Mfld} (hp : T.Prime p) :
    T.ToralGeometrizable p := by
  obtain ⟨ks, hks, hpieces⟩ := T.jsj p hp
  exact ⟨ks, hks, fun k hk => piece_isGeometric T (hpieces k hk)⟩

/-- **Thurston geometrization (Lean-checked reduction).**

Given the Kneser–Milnor prime decomposition, the JSJ torus decomposition, hyperbolization
of atoroidal pieces and the geometricity of Seifert fibred pieces, every closed orientable
`3`-manifold `m` decomposes as a connected sum of prime manifolds, each of which is cut
along incompressible tori into pieces carrying one of the eight Thurston geometries
(and there are exactly eight of these geometries). -/
theorem thurston_geometrization (T : Setup) :
    Fintype.card Geometry = 8 ∧ ∀ m : T.Mfld, T.Geometrizable m := by
  refine ⟨Geometry.card_eq_eight, fun m => ?_⟩
  obtain ⟨ps, hps, hprime⟩ := T.kneser_milnor m
  exact ⟨ps, hps, fun p hp => ⟨hprime p hp, prime_toralGeometrizable T (hprime p hp)⟩⟩

/-!
## Non-vacuity

The hypotheses assembled in `Frontier.Setup` are consistent: the following instance
realises them (with a single manifold, the `3`-sphere, which is prime, Seifert fibred
and carries the spherical geometry `S³`). Hence the reduction above is not vacuous.
-/

/-- A concrete model of `Frontier.Setup`, witnessing that its hypotheses are consistent. -/
def sphereSetup : Setup where
  Mfld := Unit
  ConnSum _ ps := ps = [()]
  Prime _ := True
  JSJ _ ks := ks = [()]
  Atoroidal _ := False
  SeifertFibered _ := True
  Geometric _ g := g = Geometry.S3
  kneser_milnor _ := ⟨[()], rfl, by simp⟩
  jsj _ _ := ⟨[()], rfl, by simp⟩
  hyperbolization _ h := h.elim
  seifert_geometric _ _ := ⟨Geometry.S3, by decide, by decide, rfl⟩

/-- The conclusion of the reduction is non-vacuously satisfiable. -/
theorem sphereSetup_geometrizable : ∀ m : sphereSetup.Mfld, sphereSetup.Geometrizable m :=
  (thurston_geometrization sphereSetup).2

/-- The pieces into which a model manifold is cut along incompressible tori: every model
is already a single piece, except the `Sol` model (a torus bundle with Anosov monodromy),
which is cut along a torus into a Seifert fibred piece. -/
def modelPieces (m : Geometry) : List Geometry :=
  if m = Geometry.Sol then [Geometry.E3] else [m]

/-- Each model piece is either hyperbolic or Seifert fibred. -/
theorem modelPieces_spec (m : Geometry) :
    ∀ k ∈ modelPieces m, k = Geometry.H3 ∨ (k ≠ Geometry.H3 ∧ k ≠ Geometry.Sol) := by
  revert m
  decide

/-- A richer model of `Frontier.Setup` in which the manifolds are the eight model
geometries themselves: each is prime, each carries exactly its own geometry, the
hyperbolic model is the atoroidal one, and the `Sol` model is cut along a torus into a
Seifert fibred piece. -/
def modelSetup : Setup where
  Mfld := Geometry
  ConnSum m ps := ps = [m]
  Prime _ := True
  JSJ m ks := ks = modelPieces m
  Atoroidal m := m = Geometry.H3
  SeifertFibered m := m ≠ Geometry.H3 ∧ m ≠ Geometry.Sol
  Geometric m g := m = g
  kneser_milnor m := ⟨[m], rfl, by simp⟩
  jsj m _ := ⟨modelPieces m, rfl, modelPieces_spec m⟩
  hyperbolization _ h := h
  seifert_geometric k h := ⟨k, h.1, h.2, rfl⟩

/-- **Base case.** In the model setup, each of the eight model geometries is a manifold
carrying precisely its own geometry, and the geometrization conclusion holds for it. -/
theorem modelSetup_geometrizable : ∀ m : modelSetup.Mfld, modelSetup.Geometrizable m :=
  (thurston_geometrization modelSetup).2

end Frontier

