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

namespace Chem

open Matrix

/-- `ec n m = exp (2 π i m / n)`, an `n`-th root of unity raised to the power `m`. -/

lemma ec_add_neg (n : ℕ) (k : ℕ) : ec n k + ec n (-(k : ℤ)) = (huckelEnergy n k : ℂ) := by
  have h : ((2 * Real.pi * k / n : ℝ) : ℂ) * Complex.I
      = 2 * Real.pi * Complex.I * (k : ℂ) / (n : ℂ) := by push_cast; ring
  rw [ec, ec, huckelEnergy]
  push_cast
  rw [← h, show (2 * (Real.pi : ℂ) * Complex.I * (-(k : ℂ)) / (n : ℂ))
      = -(((2 * Real.pi * k / n : ℝ) : ℂ)) * Complex.I by push_cast; ring,
    ← Complex.two_cos]
  push_cast
  ring

/-- Orthogonality of the additive characters of `ZMod n`. -/
