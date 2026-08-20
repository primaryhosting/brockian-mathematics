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

lemma sum_pow_eq_zero {ζ : ℂ} {N : ℕ} (hN : ζ ^ N = 1) (hne : ζ ≠ 1) :
    ∑ k ∈ Finset.range N, ζ ^ k = 0 := by
  rw [geom_sum_eq hne, hN, sub_self, zero_div]

/-- The root of unity `exp (2 π i d / N)` equals `1` only when `N ∣ d`. -/
