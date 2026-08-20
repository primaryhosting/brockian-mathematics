/-
# Ghz 5 Normalized
Category: Quantum Computing
Target: QC.ghz5_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

/-- Computational basis states of a 5-qubit register are indexed by `Fin 5 → Bool`. -/
abbrev Qubits5 := Fin 5 → Bool

/-- The all-zeros bit string `|00000⟩`. -/

theorem norm_sq_coeff (x : Qubits5) :
    ‖ghz5.ofLp x‖ ^ 2 = (if x = allZeros then (1 / 2 : ℝ) else 0)
      + (if x = allOnes then (1 / 2 : ℝ) else 0) := by
  have habs : ‖((1 / Real.sqrt 2 : ℝ) : ℂ)‖ ^ 2 = 1 / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / Real.sqrt 2), div_pow,
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  rw [ghz5_apply]
  by_cases h0 : x = allZeros
  · subst h0
    rw [if_pos rfl, if_pos rfl, if_neg allZeros_ne_allOnes, habs]
    norm_num
  · by_cases h1 : x = allOnes
    · subst h1
      rw [if_neg h0, if_pos rfl, if_neg h0, if_pos rfl, habs]
      norm_num
    · rw [if_neg h0, if_neg h1, if_neg h0, if_neg h1]
      norm_num

/-- The 5-qubit GHZ state `(|00000⟩ + |11111⟩)/√2` is a unit vector. -/
