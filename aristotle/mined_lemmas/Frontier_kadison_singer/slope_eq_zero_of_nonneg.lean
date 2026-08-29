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

lemma slope_eq_zero_of_nonneg {c m : ℂ}
    (h : ∀ t : ℝ, ∃ r : ℝ, 0 ≤ r ∧ c + (t : ℂ) * m = (r : ℂ)) : m = 0 := by
  obtain ⟨r₀, hr₀, h₀⟩ := h 0
  obtain ⟨r₁, hr₁, h₁⟩ := h 1
  have hc : c = (r₀ : ℂ) := by simpa using h₀
  have hm : m = ((r₁ - r₀ : ℝ) : ℂ) := by
    have : (r₀ : ℂ) + m = (r₁ : ℂ) := by simpa [hc] using h₁
    push_cast
    linear_combination this
  set a : ℝ := r₁ - r₀ with ha
  by_contra hne
  have ha0 : a ≠ 0 := by
    intro h'
    exact hne (by simp [hm, h'])
  obtain ⟨r, hr, hEq⟩ := h (-(r₀ + 1) / a)
  rw [hc, hm] at hEq
  have hEqR : r₀ + (-(r₀ + 1) / a) * a = r := by exact_mod_cast hEq
  rw [div_mul_cancel₀ _ ha0] at hEqR
  linarith

/-- Expansion of an arbitrary linear functional on matrices in the matrix units. -/
