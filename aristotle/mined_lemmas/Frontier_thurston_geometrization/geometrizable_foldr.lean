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

theorem geometrizable_foldr (T : ThreeManifoldData)
    (hsphere : T.pieces T.sphere = [])
    (hsum : ∀ M N : T.Closed, T.pieces (T.connSum M N) = T.pieces M ++ T.pieces N)
    (l : List T.Closed) (hl : ∀ M ∈ l, T.Geometrizable M) :
    T.Geometrizable (l.foldr T.connSum T.sphere) := by
  induction l with
  | nil =>
      intro P hP
      rw [List.foldr_nil, hsphere] at hP
      simp at hP
  | cons a t ih =>
      refine geometrizable_connSum T hsum (hl a (by simp)) (ih ?_)
      intro M hM
      exact hl M (by simp [hM])

/-! ## The geometrization theorem (Thurston–Perelman), as a Lean-checked
reduction

The statement below is the geometrization theorem for closed oriented
3-manifolds: every such manifold splits, along essential spheres and tori, into
pieces each of which carries one of the eight Thurston geometries.  It is
derived here from the standard structural inputs, each supplied as an explicit
hypothesis:

* Kneser–Milnor prime decomposition (`hKM`), together with additivity of the
  JSJ pieces under connected sum (`hsum`, `hsphere`);
* the JSJ trichotomy for prime manifolds (`hJSJ`);
* the geometrization of Seifert fibred pieces (`hSeifert`) and of Sol pieces
  (`hSol`);
* Thurston's hyperbolization theorem, in the form of Perelman's geometrization
  of atoroidal pieces (`hHyp`).
-/
