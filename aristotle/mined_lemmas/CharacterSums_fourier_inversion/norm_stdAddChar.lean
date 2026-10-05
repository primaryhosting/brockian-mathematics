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

theorem norm_stdAddChar (x : ZMod q) : ‖ZMod.stdAddChar x‖ = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

