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

open scoped ComplexConjugate

/-- Computational basis states of 4 qubits, indexed by bit strings `Fin 4 → Fin 2`. -/
abbrev Qubits4 := Fin 4 → Fin 2

/-- The all-zeros bit string `|0000⟩`. -/

lemma ghz4_apply_sq (i : Qubits4) :
    ‖ghz4 i‖ ^ 2 = if i ∈ ({allZero, allOne} : Finset Qubits4) then (1 / 2 : ℝ) else 0 := by
  by_cases h : i = allZero ∨ i = allOne
  · have hmem : i ∈ ({allZero, allOne} : Finset Qubits4) := by
      simpa [Finset.mem_insert] using h
    rw [if_pos hmem]
    simp only [ghz4, WithLp.ofLp_toLp, if_pos h, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity), div_pow, one_pow,
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  · have hmem : i ∉ ({allZero, allOne} : Finset Qubits4) := by
      simpa [Finset.mem_insert] using h
    rw [if_neg hmem]
    simp only [ghz4, WithLp.ofLp_toLp, if_neg h, norm_zero]
    norm_num

/-- The 4-qubit GHZ state `(|0000⟩ + |1111⟩)/√2` is a unit vector. -/
