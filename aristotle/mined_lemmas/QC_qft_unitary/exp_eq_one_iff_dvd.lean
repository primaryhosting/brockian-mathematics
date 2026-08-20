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

lemma exp_eq_one_iff_dvd {N : ℕ} (hN : 0 < N) (d : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I * (d : ℂ) / (N : ℂ)) = 1 ↔ (N : ℤ) ∣ d := by
  have hNc : (N : ℂ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr hN.ne'
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    field_simp at hm
    exact_mod_cast hm
  · rintro ⟨m, rfl⟩
    refine ⟨m, ?_⟩
    push_cast
    field_simp

/-- `exp (2 π i d / N)` is an `N`-th root of unity. -/
