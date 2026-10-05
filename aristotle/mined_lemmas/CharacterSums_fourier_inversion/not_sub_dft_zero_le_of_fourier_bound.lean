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

set_option grind.warning false

open Finset

-- Everything lives in this namespace so that `fourier` refers to the discrete Fourier
-- transform defined below rather than to Mathlib's `fourier` on `AddCircle`.
namespace CharacterSums

variable {q : ℕ} [NeZero q]

/-- The (unnormalised) discrete Fourier transform on `ZMod q`. -/

theorem not_sub_dft_zero_le_of_fourier_bound :
    ¬ ∀ (q : ℕ) [NeZero q] (f : ZMod q → ℂ) (B : ℝ),
        (∀ k : ZMod q, k ≠ 0 → ‖fourier f k‖ ≤ B) → ∀ x : ZMod q,
          ‖f x - fourier f 0‖ ≤ (q - 1 : ℕ) * B := by
  intro h
  have hchar : (ZMod.stdAddChar (1 : ZMod 2)) = -1 := by
    have h2 := ZMod.stdAddChar_coe (N := 2) 1
    push_cast at h2
    rw [h2, show (2 * Real.pi * Complex.I * 1 / 2) = Real.pi * Complex.I by ring]
    exact Complex.exp_pi_mul_I
  have hu : (univ : Finset (ZMod 2)) = {0, 1} := by decide
  set f : ZMod 2 → ℂ := fun _ => 1 with hf
  have hB : ∀ k : ZMod 2, k ≠ 0 → ‖fourier f k‖ ≤ 0 := by
    intro k hk
    have hk1 : k = 1 := by revert hk; revert k; decide
    subst hk1
    have : fourier f (1 : ZMod 2) = 0 := by
      rw [fourier_apply]
      rw [hu, Finset.sum_insert (by decide), Finset.sum_singleton]
      norm_num [hf]
      rw [show (-(1 : ZMod 2)) = 1 by decide, hchar]
      simp
    rw [this, norm_zero]
  have hmain := h 2 f 0 hB 0
  have hzero : fourier f (0 : ZMod 2) = 2 := by
    rw [fourier_apply]
    rw [hu, Finset.sum_insert (by decide), Finset.sum_singleton]
    norm_num [hf]
  rw [hzero] at hmain
  norm_num [hf] at hmain

/--
Corrected form of the requested statement: a uniform bound `B` on the nonzero Fourier
coefficients of `f` bounds the deviation of `f` from its mean `(q : ℂ)⁻¹ * fourier f 0`
by `(q - 1) * B`.
-/
