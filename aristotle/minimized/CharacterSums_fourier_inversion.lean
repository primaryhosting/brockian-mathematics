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

noncomputable def fourier (f : ZMod q → ℂ) : ZMod q → ℂ := ZMod.dft f

theorem fourier_inversion (f : ZMod q → ℂ) (x : ZMod q) :
    f x = (q : ℂ)⁻¹ * ∑ a : ZMod q, ZMod.stdAddChar (a * x) * fourier f a := by
  calc
    f x = (ZMod.dft.symm (ZMod.dft f)) x := by simp
    _ = (q : ℂ)⁻¹ * ∑ a : ZMod q, ZMod.stdAddChar (a * x) * fourier f a := by
        simp only [ZMod.invDFT_apply, fourier, smul_eq_mul]
