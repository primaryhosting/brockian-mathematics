/-
# Qft Unitary 4
Category: Quantum Computing
Target: QC.qft_unitary_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Qft Unitary 4
Category: Quantum Computing
Target: QC.qft_unitary_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- A primitive `16`-th root of unity, `exp (2πi/16)`. -/

theorem qft_unitary_4 : qftMatrix4 ∈ Matrix.unitaryGroup (Fin 16) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i k
  rw [Matrix.mul_apply]
  have key : ∀ j : Fin 16, qftMatrix4 i j * (star qftMatrix4) j k
      = (omega16 ^ i.val / omega16 ^ k.val) ^ j.val / 16 := by
    intro j
    show omega16 ^ (i.val * j.val) / 4 * star (omega16 ^ (k.val * j.val) / 4) = _
    rw [star_div₀, star_omega16_pow, pow_mul, pow_mul, div_pow,
      show star (4 : ℂ) = 4 by norm_num]
    ring
  rw [Finset.sum_congr rfl (fun j _ => key j), ← Finset.sum_div, geom_sum_omega16]
  by_cases h : i = k <;> simp [h, Matrix.one_apply]

/-- Restatement: the conjugate transpose of the 4-qubit QFT matrix is its inverse. -/
