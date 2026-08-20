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

theorem grover_optimal_one {N M T : ℕ} (U : ℕ → (State N M ≃ₗᵢ[ℂ] State N M))
    (psi0 : State N M) (hpsi0 : ‖psi0‖ = 1)
    (hdist : ∀ i : Fin N, 1 ≤ ‖run U psi0 (oracle i) T - run U psi0 id T‖) :
    √N / 2 ≤ T := by
  have := grover_optimal U psi0 hpsi0 1 zero_le_one hdist
  linarith [this]

/-- The hypotheses of `grover_optimal` are satisfiable, so the statement is not vacuous:
on a one-element database a single query already separates the marked oracle from the
unmarked one by the maximal distance `2`, and the bound `T ≥ (c/2)·√N` is then tight
(`(2/2)·√1 = 1 ≤ 1`). -/
