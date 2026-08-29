import Mathlib

/-!
# Kadison Singer
Category: Frontier — Fields Medal Work
Target: Frontier.kadison_singer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A *state* on the matrix algebra `M_n(ℂ)`: a unital positive linear functional.
Positivity is expressed by requiring `f (Xᴴ * X)` to be a nonnegative real number. -/
structure IsState (f : Matrix n n ℂ →ₗ[ℂ] ℂ) : Prop where
  unital : f 1 = 1
  pos : ∀ X : Matrix n n ℂ, ∃ r : ℝ, 0 ≤ r ∧ f (Xᴴ * X) = (r : ℂ)

/-- `f` extends the pure state `d ↦ d i` of the diagonal MASA `D_n ⊆ M_n(ℂ)`.
(The pure states of the commutative algebra `D_n ≃ ℂ^n` are exactly the evaluations.) -/

def entryFunctional (i : n) : Matrix n n ℂ →ₗ[ℂ] ℂ where
  toFun A := A i i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype n] [DecidableEq n] in
