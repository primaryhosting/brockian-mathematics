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

lemma sum_markSq (psi : State N M) : ∑ i : Fin N, markSq i psi = ‖psi‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  rfl

/-- A query to the oracle for `i` disturbs `psi` by exactly twice the amplitude that
`psi` places on the index `i`. -/
