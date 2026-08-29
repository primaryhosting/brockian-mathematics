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

lemma offdiag_eq_zero (hf : IsState f) {k l : n} (hkl : k ≠ l)
    (hkk : f (Matrix.single k k 1) = 0) :
    f (Matrix.single k l 1) = 0 ∧ f (Matrix.single l k 1) = 0 := by
  set u : ℂ := f (Matrix.single k l 1) with hu
  set v : ℂ := f (Matrix.single l k 1) with hv
  set c : ℂ := f (Matrix.single l l 1) with hc
  have h1 : u + v = 0 := by
    refine slope_eq_zero_of_nonneg (c := c) ?_
    intro t
    obtain ⟨r, hr, hEq⟩ := state_pos_pair hf hkl (t : ℂ) 1
    refine ⟨r, hr, ?_⟩
    rw [← hEq, hkk]
    simp only [map_one, Complex.conj_ofReal, ← hu, ← hv, ← hc]
    ring
  have h2 : Complex.I * (v - u) = 0 := by
    refine slope_eq_zero_of_nonneg (c := c) ?_
    intro t
    obtain ⟨r, hr, hEq⟩ := state_pos_pair hf hkl ((t : ℂ) * Complex.I) 1
    refine ⟨r, hr, ?_⟩
    rw [← hEq, hkk]
    simp only [map_one, map_mul, Complex.conj_ofReal, Complex.conj_I, ← hu, ← hv, ← hc]
    ring
  have h3 : v - u = 0 := by
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h Complex.I_ne_zero
    · exact h
  exact ⟨by linear_combination (h1 - h3) / 2, by linear_combination (h1 + h3) / 2⟩

end Core

/-! ### Pure states of the diagonal MASA -/

/-- The pure states of the commutative algebra `D_n ≃ ℂ^n` (equivalently, its characters:
unital multiplicative linear functionals) are exactly the coordinate evaluations
`d ↦ d i`.  This justifies the definition of `Frontier.ExtendsDiagonalPureState`. -/
