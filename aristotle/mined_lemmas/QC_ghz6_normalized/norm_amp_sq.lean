/-
# Ghz 6 Normalized
Category: Quantum Computing
Target: QC.ghz6_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

/-- The state space of 6 qubits: the (finite-dimensional) Hilbert space of complex
amplitudes indexed by bit strings `Fin 6 → Fin 2`. -/
abbrev Qubits6 : Type := EuclideanSpace ℂ (Fin 6 → Fin 2)

/-- The all-zeros bit string `|000000⟩`. -/

lemma norm_amp_sq : ‖((1 / Real.sqrt 2 : ℝ) : ℂ)‖ ^ 2 = 1 / 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0)]

/-- The 6-qubit GHZ state `(|0…0⟩ + |1…1⟩)/√2` is a unit vector. -/
