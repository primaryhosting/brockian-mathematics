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

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QC

/-- The `N × N` discrete Fourier transform (QFT) matrix:
`F j k = exp (2 π i j k / N) / √N`. -/

theorem dft_unitary (N : ℕ) (hN : N ≠ 0) : dftMatrix N ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext j k
  rw [Matrix.mul_apply]
  have hNpos : (0:ℝ) < N := by positivity
  have hsq : ((Real.sqrt N : ℝ) : ℂ) * ((Real.sqrt N : ℝ) : ℂ) = (N : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (le_of_lt hNpos)]
    simp
  have key := dft_col_orthogonal N hN j k
  have hterm : ∀ m : Fin N, star (dftMatrix N) j m * dftMatrix N m k
      = ((starRingEnd ℂ) (omegaN N ^ (m.val * j.val)) * omegaN N ^ (m.val * k.val))
        / (N : ℂ) := by
    intro m
    rw [Matrix.star_apply, dftMatrix_apply, dftMatrix_apply, Complex.star_def, map_div₀,
      Complex.conj_ofReal, div_mul_div_comm, hsq]
  simp_rw [hterm, ← Finset.sum_div, key]
  by_cases hjk : j = k
  · subst hjk
    have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast hN
    simp [hNne]
  · simp [hjk]

/-- The 6-qubit quantum Fourier transform matrix is unitary. -/
