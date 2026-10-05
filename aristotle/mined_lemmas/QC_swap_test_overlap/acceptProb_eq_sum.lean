import Mathlib

/-!
# Swap Test Overlap
Category: Quantum Computing
Target: QC.swap_test_overlap
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace QC

/-!
## Model

We model the SWAP test on two `n`-level registers together with one ancilla qubit.
A pure state of the whole system is a function

  `Bool × Fin n × Fin n → ℂ`,

the first component indexing the ancilla qubit.

The circuit is: prepare `|0⟩ ⊗ ψ ⊗ φ`, apply a Hadamard gate on the ancilla,
apply a controlled SWAP of the two registers (controlled on the ancilla),
apply a Hadamard gate on the ancilla again, and finally measure the ancilla.
The test *accepts* when the ancilla is measured in the state `|0⟩`.
-/

variable {n : ℕ}

/-- The Hadamard gate acting on the ancilla qubit. -/

theorem acceptProb_eq_sum (psi phi : Fin n → ℂ) :
    acceptProb psi phi
      = (1 / 4) * ∑ i : Fin n, ∑ j : Fin n,
          Complex.normSq (psi i * phi j + psi j * phi i) := by
  simp only [acceptProb, swapTestState_false, Complex.sq_norm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [Complex.normSq_div]
  simp [Complex.normSq_apply]
  ring

/-- **The SWAP test accepts with probability `(1 + |⟨ψ|φ⟩|²)/2`.** -/
