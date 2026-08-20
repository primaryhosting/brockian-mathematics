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

namespace QC

open Complex Finset

/-- The `n`-qubit quantum Fourier transform matrix, of size `2 ^ n × 2 ^ n`:
`(QFT)_{j,k} = (1 / √(2^n)) * exp (2 π i j k / 2^n)`. -/

noncomputable def qft (n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  fun j k =>
    (Real.sqrt ((2 ^ n : ℕ) : ℝ) : ℂ)⁻¹ *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((j : ℕ) : ℂ) * ((k : ℕ) : ℂ) /
        ((2 ^ n : ℕ) : ℂ))

/-- If `ζ` is an `N`-th root of unity different from `1`, the sum of its powers vanishes. -/
