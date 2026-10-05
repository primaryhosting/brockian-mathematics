import Mathlib

/-!
# Hadamard Involutive
Category: Quantum Computing
Target: QC.hadamard_involutive
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Matrix Complex

/-- The normalization constant `1/√2` of the Hadamard gate, as a complex number. -/

lemma hc_sq : hc * hc = 1 / 2 := by
  have h2 : (0:ℝ) ≤ 2 := by norm_num
  have : ((Real.sqrt 2)⁻¹ : ℝ) * ((Real.sqrt 2)⁻¹ : ℝ) = 1 / 2 := by
    rw [← mul_inv, Real.mul_self_sqrt h2]
    norm_num
  simp only [hc, ← Complex.ofReal_mul, this]
  norm_num

/-- The Hadamard gate is Hermitian (self-adjoint). -/
