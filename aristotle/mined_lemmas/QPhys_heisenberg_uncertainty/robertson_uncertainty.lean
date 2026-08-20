import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QPhys

local notation "⟪" x ", " y "⟫" => inner ℂ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- An operator `A` on a complex inner product space is *symmetric* (formally self-adjoint)
when `⟪A x, y⟫ = ⟪x, A y⟫` for all `x, y`. -/

theorem robertson_uncertainty {A B : E →ₗ[ℂ] E}
    (hA : IsSymmetricOp A) (hB : IsSymmetricOp B) (ψ : E) :
    ‖⟪ψ, A (B ψ) - B (A ψ)⟫‖ ≤ 2 * (stdDev A ψ * stdDev B ψ) := by
  set a : ℝ := expect A ψ with ha
  set b : ℝ := expect B ψ with hb
  set u : E := A ψ - (a : ℂ) • ψ with hu
  set v : E := B ψ - (b : ℂ) • ψ with hv
  set c : ℂ := ⟪ψ, A (B ψ) - B (A ψ)⟫ with hc
  have hkey : ⟪u, v⟫ - (starRingEnd ℂ) (⟪u, v⟫) = c := by
    rw [inner_conj_symm, hu, hv, inner_shift_sub_conj hA hB ψ a b]
  -- `c` is purely imaginary, with `c.im = 2 * (⟪u, v⟫).im`
  have hre : c.re = 0 := by
    have := congrArg Complex.re hkey
    simp only [Complex.sub_re, Complex.conj_re] at this
    linarith
  have him : c.im = 2 * (⟪u, v⟫).im := by
    have := congrArg Complex.im hkey
    simp only [Complex.sub_im, Complex.conj_im] at this
    linarith
  have hnorm : ‖c‖ = |c.im| := by
    rw [Complex.norm_def, Complex.normSq_apply, hre]
    rw [show (0 : ℝ) * 0 + c.im * c.im = c.im ^ 2 by ring, Real.sqrt_sq_eq_abs]
  rw [hnorm, him, abs_mul, abs_two]
  have h1 : |(⟪u, v⟫).im| ≤ ‖⟪u, v⟫‖ := Complex.abs_im_le_norm _
  have h2 : ‖⟪u, v⟫‖ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm u v
  have : |(⟪u, v⟫).im| ≤ stdDev A ψ * stdDev B ψ := le_trans h1 h2
  linarith

/-- **Heisenberg uncertainty principle.**

Let `A` and `B` be symmetric (self-adjoint) operators on a complex inner product space `E`
satisfying the canonical commutation relation `[A, B] ψ = i ℏ ψ` on a normalized state `ψ`.
Then the product of the uncertainties satisfies `Δ A · Δ B ≥ ℏ / 2`.

With `A = x̂`, `B = p̂` this is `Δx · Δp ≥ ℏ / 2`. -/
