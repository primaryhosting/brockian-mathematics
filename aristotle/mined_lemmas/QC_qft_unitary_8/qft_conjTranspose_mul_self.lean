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

namespace QC

/-- The `N × N` Quantum Fourier Transform matrix:
`(QFT N) j k = exp (2 π i j k / N) / √N`. -/

theorem qft_conjTranspose_mul_self (hN : N ≠ 0) :
    (qft N).conjTranspose * qft N = 1 := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  ext a b
  rw [Matrix.mul_apply]
  have hterm : ∀ j : Fin N, (qft N).conjTranspose a j * qft N j b
      = (1 / (N : ℂ)) * (phase N a b) ^ (j : ℕ) := by
    intro j
    rw [Matrix.conjTranspose_apply]
    exact star_qft_mul_qft hN a b j
  rw [Finset.sum_congr rfl fun j _ => hterm j, ← Finset.mul_sum,
    Fin.sum_univ_eq_sum_range (fun i => (phase N a b) ^ i) N]
  by_cases hab : a = b
  · subst hab
    rw [phase_self a]
    simp [hN']
  · rw [geom_sum_eq (phase_ne_one hN hab), phase_pow_card hN]
    simp [hab]

/-- The QFT matrix is unitary. -/
