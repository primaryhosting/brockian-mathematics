/-
# Qft Unitary 6
Category: Quantum Computing
Target: QC.qft_unitary_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Qft Unitary 6
Category: Quantum Computing
Target: QC.qft_unitary_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace QC

/-- The `n`-dimensional quantum Fourier transform matrix:
`(QFT_n)_{j k} = exp(2πi·jk/n) / √n`. -/

lemma sum_root_pow (n : ℕ) (hn : 0 < n) (d : ℤ) (hd : ¬ ((n : ℤ) ∣ d)) :
    ∑ l ∈ Finset.range n, Complex.exp (2 * Real.pi * Complex.I * (l * d) / n) = 0 := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  set x : ℂ := Complex.exp (2 * Real.pi * Complex.I * d / n) with hx
  have hterm : ∀ l ∈ Finset.range n,
      Complex.exp (2 * Real.pi * Complex.I * (l * d) / n) = x ^ l := by
    intro l _
    rw [hx, ← Complex.exp_nat_mul]
    congr 1
    field_simp
  rw [Finset.sum_congr rfl hterm]
  have hxn : x ^ n = 1 := by
    rw [hx, ← Complex.exp_nat_mul]
    have h : (n : ℂ) * (2 * Real.pi * Complex.I * d / n) = (d : ℂ) * (2 * Real.pi * Complex.I) := by
      field_simp
    rw [h, Complex.exp_int_mul_two_pi_mul_I]
  have hx1 : x ≠ 1 := by
    rw [hx, Ne, Complex.exp_eq_one_iff]
    rintro ⟨m, hm⟩
    refine hd ⟨m, ?_⟩
    have hdc : (d : ℂ) = (n : ℂ) * m := by
      field_simp at hm
      exact Complex.ext (congrArg Complex.re hm) (congrArg Complex.im hm)
    exact_mod_cast hdc
  rw [geom_sum_eq hx1, hxn, sub_self, zero_div]

/-- Conjugating one Fourier phase and multiplying by another gives the phase of the difference. -/
