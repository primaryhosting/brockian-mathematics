/-
# Ghz 4 Normalized
Category: Quantum Computing
Target: QC.ghz4_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ghz 4 Normalized
Category: Quantum Computing
Target: QC.ghz4_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- The all-zeros computational basis label `|0000⟩` for four qubits. -/

lemma norm_sq_coeff : ‖(((Real.sqrt 2)⁻¹ : ℝ) : ℂ)‖ ^ 2 = 1 / 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), inv_pow,
    Real.sq_sqrt (by norm_num)]
  norm_num

/-- `ghz4` really is `(|0000⟩ + |1111⟩)/√2`, written in terms of the computational
basis vectors `EuclideanSpace.single`. -/
