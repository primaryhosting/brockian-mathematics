/-
# Ghz 8 Normalized
Category: Quantum Computing
Target: QC.ghz8_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

/-- The state space of 8 qubits: the complex Hilbert space with orthonormal basis indexed by
the computational basis states `Fin 8 → Bool`. -/
abbrev Qubits8 := EuclideanSpace ℂ (Fin 8 → Bool)

/-- The computational basis state `|b⟩` of 8 qubits. -/

theorem norm_basisState_add_basisState {x y : Fin 8 → Bool} (h : x ≠ y) :
    ‖basisState x + basisState y‖ = Real.sqrt 2 := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  have key : ∀ b : (Fin 8 → Bool), ‖(basisState x + basisState y : Qubits8) b‖ ^ 2
      = (if b = x then (1 : ℝ) else 0) + (if b = y then 1 else 0) := by
    intro b
    by_cases hx : b = x <;> by_cases hy : b = y <;>
      simp_all [basisState, EuclideanSpace.single_apply]
  calc ∑ b : (Fin 8 → Bool), ‖(basisState x + basisState y : Qubits8) b‖ ^ 2
      = ∑ b : (Fin 8 → Bool), ((if b = x then (1 : ℝ) else 0) + (if b = y then 1 else 0)) :=
        Finset.sum_congr rfl (fun b _ => key b)
    _ = 2 := by rw [Finset.sum_add_distrib]; simp; norm_num

/-- The 8-qubit GHZ state `(|0…0⟩ + |1…1⟩)/√2` is a unit vector. -/
