import Mathlib

/-!
# Grover Optimal
Category: Frontier Qi
Target: QI.grover_optimal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

namespace QI

variable {N M : ℕ}

/-- The state space of a quantum query algorithm searching a database of size `N`:
an index register `Fin N` together with an arbitrary finite workspace `Fin M`. -/
abbrev State (N M : ℕ) : Type := EuclideanSpace ℂ (Fin N × Fin M)

/-- The standard phase oracle marking the index `i`: it flips the sign of every
amplitude whose index register holds `i`, and does nothing otherwise. -/

lemma oracle_norm (i : Fin N) (psi : State N M) : ‖oracle i psi‖ = ‖psi‖ := by
  have h : ‖oracle i psi‖ ^ 2 = ‖psi‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun jw _ => ?_
    by_cases h : jw.1 = i <;> simp [h]
  calc ‖oracle i psi‖ = √(‖oracle i psi‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = √(‖psi‖ ^ 2) := by rw [h]
    _ = ‖psi‖ := Real.sqrt_sq (norm_nonneg _)

