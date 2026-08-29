/-
# Qft Unitary 4
Category: Quantum Computing
Target: QC.qft_unitary_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header above uses a plain block comment because Lean requires `import`
-- to precede any module docstring; the docstring form is repeated below.)

import Mathlib

/-!
# Qft Unitary 4
Category: Quantum Computing
Target: QC.qft_unitary_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- The primitive `N`-th root of unity `exp (2 π i / N)` used by the quantum Fourier
transform on `N` basis states. -/

theorem qftMatrix_mem_unitaryGroup (N : ℕ) (hN : N ≠ 0) :
    qftMatrix N ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext j k
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hcast : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  simp only [qft_prod, ← Finset.mul_sum]
  by_cases hjk : j = k
  · subst hjk
    simp [hcast]
  · rw [if_neg hjk]
    have hd : ¬ ((N : ℤ) ∣ ((k : ℤ) - (j : ℤ))) := by
      intro hdvd
      have hlt : |((k : ℤ) - (j : ℤ))| < (N : ℤ) := by
        have hj : (j : ℤ) < N := by exact_mod_cast j.isLt
        have hk : (k : ℤ) < N := by exact_mod_cast k.isLt
        have hj0 : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg _
        have hk0 : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg _
        rw [abs_lt]
        omega
      have := Int.eq_zero_of_abs_lt_dvd hdvd hlt
      apply hjk
      have : (j : ℕ) = (k : ℕ) := by omega
      exact Fin.ext this
    rw [Fin.sum_univ_eq_sum_range (fun m => (qftZeta N ^ ((k : ℤ) - (j : ℤ))) ^ m) N,
      qft_geom_sum N hN _ hd, mul_zero]

/-- The 4-qubit (16-dimensional) quantum Fourier transform matrix is unitary. -/
