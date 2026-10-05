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

theorem allZeros_ne_allOnes {n : ℕ} (hn : 0 < n) : allZeros n ≠ allOnes n := by
  intro h
  have := congrFun h ⟨0, hn⟩
  simp [allZeros, allOnes] at this

/-- The norm of the unnormalized superposition `|0…0⟩ + |1…1⟩` is `√2`. -/
