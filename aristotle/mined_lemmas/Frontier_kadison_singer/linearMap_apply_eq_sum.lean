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

lemma linearMap_apply_eq_sum (f : Matrix n n ℂ →ₗ[ℂ] ℂ) (A : Matrix n n ℂ) :
    f A = ∑ q : n, ∑ s : n, A q s * f (Matrix.single q s 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single A]
  rw [map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  have : Matrix.single q s (A q s) = A q s • Matrix.single q s (1 : ℂ) := by
    simp
  rw [this, map_smul, smul_eq_mul]

/-- For a rank-one matrix built from a vector `w`, `Xᴴ * X` is the outer product. -/
