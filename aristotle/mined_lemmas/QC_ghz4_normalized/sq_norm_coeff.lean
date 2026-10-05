import Mathlib

/-!
# Ghz 4 Normalized
Category: Quantum Computing
Target: QC.ghz4_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- The computational basis of a 4-qubit system is indexed by bit strings `Fin 4 → Bool`. -/
abbrev Qubits4 := Fin 4 → Bool

/-- The all-zeros bit string, i.e. the basis label of `|0000⟩`. -/

lemma sq_norm_coeff : ‖((1 / Real.sqrt 2 : ℝ) : ℂ)‖ ^ 2 = 1 / 2 := by
  rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), div_pow, one_pow,
    Real.sq_sqrt (by norm_num)]

/-- The 4-qubit GHZ state `(|0000⟩ + |1111⟩)/√2` is a unit vector. -/
