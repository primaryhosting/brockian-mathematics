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

@[simp] theorem fourier_apply (f : ZMod q → ℂ) (a : ZMod q) :
    fourier f a = ∑ x : ZMod q, ZMod.stdAddChar (-(x * a)) * f x := by
  simp only [fourier, ZMod.dft_apply, smul_eq_mul]

/-- Fourier inversion. Note the normalising factor `(q : ℂ)⁻¹`: `fourier f 0 = ∑ x, f x` is
`q` times the mean of `f`, not the mean itself. -/
