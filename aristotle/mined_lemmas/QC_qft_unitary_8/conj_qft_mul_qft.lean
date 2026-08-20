/-
# Qft Unitary 8
Category: Quantum Computing
Target: QC.qft_unitary_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QC

/-- The `N`-dimensional quantum Fourier transform matrix:
`(QFT_N)_{j,k} = exp(2πi·j·k/N) / √N`. -/

lemma conj_qft_mul_qft (N : ℕ) (hN : 0 < N) (m j k : Fin N) :
    (starRingEnd ℂ) (qft N m j) * qft N m k
      = (zeta N ((k : ℕ) - (j : ℕ) : ℤ)) ^ (m : ℕ) / (N : ℂ) := by
  have hNne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hsq : ((Real.sqrt N : ℝ) : ℂ) * ((Real.sqrt N : ℝ) : ℂ) = (N : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg N)]
    norm_num
  have hsqne : ((Real.sqrt N : ℝ) : ℂ) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hsq
    exact hNne hsq.symm
  have hconj : (starRingEnd ℂ) (qft N m j)
      = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (((m : ℕ) * (j : ℕ) : ℕ) : ℂ) / (N : ℂ))) /
        ((Real.sqrt N : ℝ) : ℂ) := by
    rw [qft, map_div₀, ← Complex.exp_conj]
    congr 2
    · simp [Complex.ext_iff]
      ring
    · simp
  rw [hconj, qft, zeta_pow, div_mul_div_comm, ← Complex.exp_add, hsq]
  congr 2
  push_cast
  field_simp
  ring

/-- The QFT matrix satisfies `Aᴴ * A = 1`. -/
