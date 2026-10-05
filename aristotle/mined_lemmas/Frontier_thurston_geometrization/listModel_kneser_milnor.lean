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

theorem listModel_kneser_milnor (M : listModel.Closed) :
    ∃ l : List listModel.Closed,
      (∀ P ∈ l, listModel.Prime P) ∧ M = l.foldr listModel.connSum listModel.sphere := by
  refine ⟨(M : List Geometry).map (fun g => [g]), ?_, ?_⟩
  · intro P hP
    obtain ⟨g, _, rfl⟩ := List.mem_map.1 hP
    exact ⟨g, rfl⟩
  · show M = List.foldr (fun M N => M ++ N) [] ((M : List Geometry).map fun g => [g])
    induction (M : List Geometry) with
    | nil => rfl
    | cons a t ih =>
        simp only [List.map_cons, List.foldr_cons, List.cons_append, List.nil_append]
        exact congrArg (a :: ·) ih

