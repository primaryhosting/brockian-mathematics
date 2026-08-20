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

lemma norm_run_id (U : ℕ → (State N M ≃ₗᵢ[ℂ] State N M)) (psi0 : State N M) (t : ℕ) :
    ‖run U psi0 id t‖ = ‖psi0‖ := by
  induction t with
  | zero => simp
  | succ t ih => simpa using ih

/-- **Hybrid argument** (Bennett–Bernstein–Brassard–Vazirani): after `T` queries, the
state produced with the oracle for `i` differs from the state produced with no oracle
at all by at most the total disturbance the oracle for `i` would cause along the
undisturbed trajectory. -/
