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

theorem isSeifert_iff (g : Geometry) : IsSeifert g ↔ g ≠ H3 ∧ g ≠ Sol := by
  cases g <;> simp [IsSeifert]

end Geometry

/-! ## Concrete models for three of the eight geometries

`E³` is the abelian Lie group `ℝ³`; `Nil` is the three dimensional Heisenberg
group; `Sol` is the solvable group `ℝ² ⋊ ℝ`.  Each acts simply transitively on
itself, so these are genuine (distinct) model geometries.  We construct the
group structures and check that the three are pairwise non-isomorphic. -/

/-- The underlying set of the model geometry `Nil`: the Heisenberg group. -/
@[ext]
structure NilModel where
  x : ℝ
  y : ℝ
  z : ℝ

namespace NilModel

instance : Mul NilModel := ⟨fun a b => ⟨a.x + b.x, a.y + b.y, a.z + b.z + a.x * b.y⟩⟩
instance : One NilModel := ⟨⟨0, 0, 0⟩⟩
instance : Inv NilModel := ⟨fun a => ⟨-a.x, -a.y, -a.z + a.x * a.y⟩⟩

