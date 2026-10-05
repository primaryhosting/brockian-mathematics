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

theorem exists_commutator_not_central :
    ∃ a b c : SolModel, (a * b * a⁻¹ * b⁻¹) * c ≠ c * (a * b * a⁻¹ * b⁻¹) := by
  refine ⟨⟨1, 0, 0⟩, ⟨0, 0, 1⟩, ⟨0, 0, 1⟩, ?_⟩
  intro h
  have hx := congrArg SolModel.x h
  simp [Real.exp_zero, Real.exp_neg] at hx
  -- `hx` reduces to an identity forcing `Real.exp 1 = 1`
  have h1 : Real.exp 1 = 1 := by
    nlinarith [Real.exp_pos (1 : ℝ), Real.exp_pos (-1 : ℝ),
      Real.exp_ne_zero (1 : ℝ), hx]
  have : (1 : ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (x := (1 : ℝ)) (by norm_num)
    linarith
  rw [h1] at this
  exact lt_irrefl _ this

end SolModel

/-- The model geometries `Nil` and `Sol` are not isomorphic as groups: in `Nil`
all commutators are central, while in `Sol` they are not. -/
