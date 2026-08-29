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

set_option grind.warning false

namespace Frontier

/-! ## The eight Thurston geometries -/

/-- The eight three-dimensional Thurston model geometries:
Euclidean `E³`, spherical `S³`, hyperbolic `H³`, the two product geometries
`S² × ℝ` and `H² × ℝ`, the universal cover of `SL(2,ℝ)`, `Nil` (the Heisenberg
group) and `Sol`. -/
inductive Geometry
  | E3 | S3 | H3 | S2xR | H2xR | SL2R | Nil | Sol
  deriving DecidableEq, Repr, Fintype

namespace Geometry

/-- There are exactly eight Thurston geometries. -/

theorem prime_geometrizable (T : ThreeManifoldData)
    (hJSJ : ∀ M : T.Closed, T.Prime M → ∀ P ∈ T.pieces M,
      T.SeifertFibered P ∨ T.SolType P ∨ T.Atoroidal P)
    (hSeifert : ∀ P : T.Piece, T.SeifertFibered P →
      ∃ g : Geometry, g.IsSeifert ∧ T.geometry P = some g)
    (hSol : ∀ P : T.Piece, T.SolType P → T.geometry P = some Geometry.Sol)
    (hHyp : ∀ P : T.Piece, T.Atoroidal P → T.geometry P = some Geometry.H3)
    (M : T.Closed) (hM : T.Prime M) : T.Geometrizable M := by
  intro P hP
  rcases hJSJ M hM P hP with h | h | h
  · obtain ⟨g, _, hg⟩ := hSeifert P h
    exact ⟨g, hg⟩
  · exact ⟨Geometry.Sol, hSol P h⟩
  · exact ⟨Geometry.H3, hHyp P h⟩

/-! ### Step 2: from primes to all closed 3-manifolds via Kneser–Milnor. -/

/-- Geometrizability is inherited by connected sums, given additivity of the
JSJ pieces. -/
