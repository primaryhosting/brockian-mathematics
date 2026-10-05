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

lemma qft_prod (N : ℕ) (j k m : Fin N) :
    star (qftMatrix N) j m * qftMatrix N m k
      = (N : ℂ)⁻¹ * (qftZeta N ^ ((k : ℤ) - (j : ℤ))) ^ (m : ℕ) := by
  have hz : qftZeta N ≠ 0 := qftZeta_ne_zero N
  rw [Matrix.star_apply, qftMatrix_apply_pow, qftMatrix_apply_pow]
  have hstar : star (((Real.sqrt N : ℝ) : ℂ)⁻¹ * qftZeta N ^ ((m : ℕ) * (j : ℕ)))
      = ((Real.sqrt N : ℝ) : ℂ)⁻¹ * (qftZeta N)⁻¹ ^ ((m : ℕ) * (j : ℕ)) := by
    simp only [star_mul', star_inv₀, star_pow, Complex.star_def,
      Complex.conj_ofReal, qftZeta_conj]
  rw [hstar]
  have hN2 : ((Real.sqrt N : ℝ) : ℂ)⁻¹ * ((Real.sqrt N : ℝ) : ℂ)⁻¹ = (N : ℂ)⁻¹ := by
    have h : ((Real.sqrt N : ℝ) : ℂ) * ((Real.sqrt N : ℝ) : ℂ) = (N : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg N)]
      push_cast
      ring
    rw [← mul_inv, h]
  have hpow : (qftZeta N)⁻¹ ^ ((m : ℕ) * (j : ℕ)) * qftZeta N ^ ((m : ℕ) * (k : ℕ))
      = (qftZeta N ^ ((k : ℤ) - (j : ℤ))) ^ (m : ℕ) := by
    rw [← zpow_natCast (qftZeta N ^ ((k : ℤ) - (j : ℤ))) (m : ℕ), ← zpow_mul]
    rw [inv_pow, ← zpow_natCast (qftZeta N) ((m : ℕ) * (j : ℕ)),
      ← zpow_natCast (qftZeta N) ((m : ℕ) * (k : ℕ)), ← zpow_neg, ← zpow_add₀ hz]
    congr 1
    push_cast
    ring
  calc ((Real.sqrt N : ℝ) : ℂ)⁻¹ * (qftZeta N)⁻¹ ^ ((m : ℕ) * (j : ℕ)) *
        (((Real.sqrt N : ℝ) : ℂ)⁻¹ * qftZeta N ^ ((m : ℕ) * (k : ℕ)))
      = (((Real.sqrt N : ℝ) : ℂ)⁻¹ * ((Real.sqrt N : ℝ) : ℂ)⁻¹) *
        ((qftZeta N)⁻¹ ^ ((m : ℕ) * (j : ℕ)) * qftZeta N ^ ((m : ℕ) * (k : ℕ))) := by ring
    _ = (N : ℂ)⁻¹ * (qftZeta N ^ ((k : ℤ) - (j : ℤ))) ^ (m : ℕ) := by rw [hN2, hpow]

/-- The `N`-dimensional QFT matrix is unitary. -/
