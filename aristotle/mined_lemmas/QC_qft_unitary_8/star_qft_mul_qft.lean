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

private lemma star_qft_mul_qft (hN : N ≠ 0) (a b j : Fin N) :
    star (qft N j a) * qft N j b = (1 / (N : ℂ)) * (phase N a b) ^ (j : ℕ) := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have h1 : ((Real.sqrt N : ℝ) : ℂ) * ((Real.sqrt N : ℝ) : ℂ) = (N : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    simp
  rw [show star (qft N j a)
        = Complex.exp (-(2 * Real.pi * Complex.I * (j * a) / N)) / Real.sqrt N by
    simp [qft, ← Complex.exp_conj, Complex.conj_I, map_ofNat]; ring_nf]
  rw [phase, ← Complex.exp_nat_mul]
  simp only [qft, Matrix.of_apply, div_mul_div_comm, ← Complex.exp_add]
  rw [h1, one_div, ← div_eq_inv_mul]
  congr 1
  ring_nf

