/-
# Ghz 6 Normalized
Category: Quantum Computing
Target: QC.ghz6_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

/-- The computational basis of a 6-qubit system is indexed by bit strings
`Fin 6 → Fin 2`; states live in the Hilbert space `EuclideanSpace ℂ (Fin 6 → Fin 2)`
(a 64-dimensional complex inner product space). -/
abbrev Qubits6 := EuclideanSpace ℂ (Fin 6 → Fin 2)

/-- The all-zeros bit string `000000`. -/

private lemma norm_basis_sum :
    ‖(EuclideanSpace.single allZeros 1 + EuclideanSpace.single allOnes 1 : Qubits6)‖
      = Real.sqrt 2 := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  have key : ∀ i : Fin 6 → Fin 2,
      ‖(WithLp.ofLp (EuclideanSpace.single allZeros (1 : ℂ)
          + EuclideanSpace.single allOnes (1 : ℂ) : Qubits6)) i‖ ^ 2
        = (if i = allZeros then (1 : ℝ) else 0) + (if i = allOnes then (1 : ℝ) else 0) := by
    intro i
    by_cases h0 : i = allZeros <;> by_cases h1 : i = allOnes <;>
      simp [EuclideanSpace.single_apply, h0, h1, allZeros_ne_allOnes,
        Ne.symm allZeros_ne_allOnes]
  rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq']
  norm_num

/-- The 6-qubit GHZ state `(|000000⟩ + |111111⟩)/√2` is a unit vector. -/
