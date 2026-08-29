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

theorem ghz4_normalized : ‖ghz4‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have hsum : ∑ i : Qubits4, ‖ghz4.ofLp i‖ ^ 2 = 1 := by
    rw [Finset.sum_congr rfl (fun i _ => ghz4_apply_sq i)]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
      Finset.card_pair allZero_ne_allOne]
    norm_num
  rw [hsum, Real.sqrt_one]

/-- The defining description of the GHZ state: it is `(|0000⟩ + |1111⟩)/√2`, where
`|b⟩` denotes the computational basis vector `EuclideanSpace.single b 1`. -/
