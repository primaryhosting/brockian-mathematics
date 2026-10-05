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

def IsGeometric (M : T.Mfld) : Prop := ∃ G : ThurstonGeometry, T.Geometric M G

/-- Kneser–Milnor prime decomposition: every closed oriented 3-manifold is a connected sum of
finitely many prime closed oriented 3-manifolds. -/

def PrimeDecompositionAxiom : Prop :=
  ∀ M : T.Mfld, T.IsClosedOriented M →
    ∃ ps : List T.Mfld, T.ConnectedSumDecomp M ps ∧
      ∀ p ∈ ps, T.IsClosedOriented p ∧ T.IsPrime p

/-- Jaco–Shalen–Johannson torus decomposition: every prime closed oriented 3-manifold can be cut
along finitely many disjoint incompressible tori into Seifert fibred or atoroidal pieces. -/

def JSJAxiom : Prop :=
  ∀ P : T.Mfld, T.IsClosedOriented P → T.IsPrime P →
    ∃ qs : List T.Mfld, T.TorusDecomp P qs ∧ ∀ q ∈ qs, T.IsSeifertOrAtoroidal q

/-- Thurston's hyperbolization together with the geometrization of Seifert fibred spaces
(completed by Perelman): every JSJ piece is geometric. -/

def PiecesAreGeometricAxiom : Prop :=
  ∀ q : T.Mfld, T.IsSeifertOrAtoroidal q → T.IsGeometric q

/-- **The Geometrization statement.** Every closed oriented 3-manifold decomposes as a connected
sum of prime manifolds, each of which is cut by incompressible tori into pieces admitting a
geometric structure modelled on one of the eight Thurston geometries. -/

def Geometrization : Prop :=
  ∀ M : T.Mfld, T.IsClosedOriented M →
    ∃ ps : List T.Mfld, T.ConnectedSumDecomp M ps ∧
      ∀ p ∈ ps, T.IsPrime p ∧
        ∃ qs : List T.Mfld, T.TorusDecomp p qs ∧
          ∀ q ∈ qs, ∃ G : ThurstonGeometry, T.Geometric q G

end ThreeManifoldTheory

/-! ## The reduction -/

/-- **Base case of the reduction.** If a prime piece is already known to be a JSJ piece which is
cut trivially into itself, and all JSJ pieces are geometric, then it has a geometric torus
decomposition. -/

theorem thurston_geometrization (T : ThreeManifoldTheory)
    (hprime : T.PrimeDecompositionAxiom) (hjsj : T.JSJAxiom)
    (hgeo : T.PiecesAreGeometricAxiom) :
    T.Geometrization := by
  intro M hM
  obtain ⟨ps, hps, hps'⟩ := hprime M hM
  refine ⟨ps, hps, ?_⟩
  intro p hp
  obtain ⟨hpClosed, hpPrime⟩ := hps' p hp
  refine ⟨hpPrime, ?_⟩
  obtain ⟨qs, hqs, hqs'⟩ := hjsj p hpClosed hpPrime
  exact ⟨qs, hqs, fun q hq => hgeo q (hqs' q hq)⟩

/-! ## The hypotheses are consistent

To make sure that the statement above is not vacuous we exhibit a concrete interface satisfying
all three hypotheses (and hence, by the theorem, the geometrization conclusion): the "manifolds"
are the eight model geometries themselves, each one prime, each one its own JSJ piece, and each
one geometric for its own geometry. -/

/-- A toy model of the interface: the model geometries themselves. -/
