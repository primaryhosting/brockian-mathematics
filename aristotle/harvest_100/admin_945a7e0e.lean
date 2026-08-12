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
def IsSymmetricOp (A : E →ₗ[ℂ] E) : Prop := ∀ x y : E, ⟪A x, y⟫ = ⟪x, A y⟫

/-- The expectation value `⟪ψ, A ψ⟫` of the observable `A` in the state `ψ`.
For a symmetric `A` and a normalized `ψ` this is a real number. -/
noncomputable def expect (A : E →ₗ[ℂ] E) (ψ : E) : ℝ := (⟪ψ, A ψ⟫).re

/-- The standard deviation (uncertainty) `Δ A = ‖(A - ⟨A⟩) ψ‖` of the observable `A`
in the state `ψ`. -/
noncomputable def stdDev (A : E →ₗ[ℂ] E) (ψ : E) : ℝ :=
  ‖A ψ - ((expect A ψ : ℝ) : ℂ) • ψ‖

/-- For a symmetric operator the expectation value is real, i.e. `⟪ψ, A ψ⟫ = ⟨A⟩`. -/
lemma inner_self_eq_expect {A : E →ₗ[ℂ] E} (hA : IsSymmetricOp A) (ψ : E) :
    ⟪ψ, A ψ⟫ = ((expect A ψ : ℝ) : ℂ) := by
  have h : (starRingEnd ℂ) (⟪ψ, A ψ⟫) = ⟪ψ, A ψ⟫ := by
    rw [inner_conj_symm]
    exact hA ψ ψ
  have := Complex.conj_eq_iff_im.mp h
  simp [expect, Complex.ext_iff, this]

/-- **Key algebraic step.** For symmetric `A`, `B` and real shifts `a`, `b`, the
anti-symmetric part of `⟪(A - a) ψ, (B - b) ψ⟫` is the expectation of the commutator. -/
lemma inner_shift_sub_conj {A B : E →ₗ[ℂ] E} (hA : IsSymmetricOp A) (hB : IsSymmetricOp B)
    (ψ : E) (a b : ℝ) :
    ⟪A ψ - (a : ℂ) • ψ, B ψ - (b : ℂ) • ψ⟫ - ⟪B ψ - (b : ℂ) • ψ, A ψ - (a : ℂ) • ψ⟫
      = ⟪ψ, A (B ψ) - B (A ψ)⟫ := by
  have hAB : ⟪A ψ, B ψ⟫ = ⟪ψ, A (B ψ)⟫ := hA ψ (B ψ)
  have hBA : ⟪B ψ, A ψ⟫ = ⟪ψ, B (A ψ)⟫ := hB ψ (A ψ)
  have hAs : ⟪A ψ, ψ⟫ = ⟪ψ, A ψ⟫ := hA ψ ψ
  have hBs : ⟪B ψ, ψ⟫ = ⟪ψ, B ψ⟫ := hB ψ ψ
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal]
  rw [hAB, hBA, hAs, hBs]
  ring

/-- **Robertson uncertainty relation.**

For symmetric operators `A`, `B` on a complex inner product space and any state `ψ`,
`|⟪ψ, [A, B] ψ⟫| ≤ 2 · Δ A · Δ B`. -/
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
theorem heisenberg_uncertainty {A B : E →ₗ[ℂ] E}
    (hA : IsSymmetricOp A) (hB : IsSymmetricOp B)
    (hbar : ℝ) (ψ : E) (hψ : ‖ψ‖ = 1)
    (hcomm : A (B ψ) - B (A ψ) = ((Complex.I * (hbar : ℂ)) : ℂ) • ψ) :
    hbar / 2 ≤ stdDev A ψ * stdDev B ψ := by
  -- the expectation of the commutator is exactly `i ℏ`
  have hψψ : ⟪ψ, ψ⟫ = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hψ]; norm_num
  have hcomm' : ⟪ψ, A (B ψ) - B (A ψ)⟫ = Complex.I * (hbar : ℂ) := by
    rw [hcomm, inner_smul_right, hψψ, mul_one]
  have hbar_le : hbar ≤ ‖⟪ψ, A (B ψ) - B (A ψ)⟫‖ := by
    rw [hcomm', norm_mul, Complex.norm_I, one_mul, Complex.norm_real]
    exact le_abs_self hbar
  have := robertson_uncertainty hA hB ψ
  linarith

end QPhys

