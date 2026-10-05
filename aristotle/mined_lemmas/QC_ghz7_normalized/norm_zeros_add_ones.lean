/-
# Ghz 7 Normalized
Category: Quantum Computing
Target: QC.ghz7_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

/-- The state space of `n` qubits, realized as the Hilbert space `ℂ^(2^n)` with
basis vectors indexed by bit strings `Fin n → Fin 2`. -/
abbrev QubitState (n : ℕ) := EuclideanSpace ℂ (Fin n → Fin 2)

/-- The all-zeros bit string `0…0`, indexing the basis vector `|0…0⟩`. -/

theorem norm_zeros_add_ones {n : ℕ} (hn : 0 < n) :
    ‖(EuclideanSpace.single (allZeros n) (1 : ℂ) +
      EuclideanSpace.single (allOnes n) 1)‖ = Real.sqrt 2 := by
  have hne : allZeros n ≠ allOnes n := allZeros_ne_allOnes hn
  rw [EuclideanSpace.norm_eq]
  congr 1
  rw [Finset.sum_congr rfl
    (g := fun x => (if x = allZeros n then (1 : ℝ) else 0) +
      (if x = allOnes n then 1 else 0))]
  · rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
    norm_num
  · intro x _
    by_cases hx : x = allZeros n <;> by_cases hy : x = allOnes n <;>
      simp_all [EuclideanSpace.single_apply]

/-- The `n`-qubit GHZ state is a unit vector, for every `n ≥ 1`. -/
