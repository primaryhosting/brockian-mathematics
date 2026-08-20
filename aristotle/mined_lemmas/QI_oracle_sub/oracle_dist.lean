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

lemma oracle_dist (i : Fin N) (psi phi : State N M) :
    ‖oracle i psi - oracle i phi‖ = ‖psi - phi‖ := by
  rw [← oracle_sub, oracle_norm]

/-- The squared norm of the part of `psi` whose index register holds `i`. -/
