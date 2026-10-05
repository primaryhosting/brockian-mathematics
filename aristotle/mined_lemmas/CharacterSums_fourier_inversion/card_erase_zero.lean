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

theorem card_erase_zero : (univ.erase (0 : ZMod q)).card = (q - 1 : ℕ) := by
  rw [Finset.card_erase_of_mem (mem_univ _), Finset.card_univ, ZMod.card]

/-- The mean of `f` is `(q : ℂ)⁻¹ * fourier f 0`, and the deviation of `f` from its mean at
any point is controlled by the nonzero Fourier coefficients, with the sharp constant
`(q - 1) / q`. -/
