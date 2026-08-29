/-
/-!
# Grover Optimal
Category: Frontier Qi
Target: QI.grover_optimal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/
-- (Lean requires `import` before any module docstring, so the required header block
-- above is enclosed in an ordinary block comment; its text is reproduced verbatim.)

import Mathlib

/-!
## The BBBV lower bound for unstructured search

We formalise the hybrid argument of Bennett–Bernstein–Brassard–Vazirani: any quantum
algorithm that finds a marked element among `N` possibilities with success probability
at least `2/3` must make `Ω(√N)` queries to the phase oracle.  In particular Grover's
algorithm, which uses `O(√N)` queries, is optimal up to a constant factor.

**The model.**  The state space is `QState N W = EuclideanSpace ℂ (Fin N × Fin W)`: the
first factor is the query register (holding an index `i < N`), the second factor is an
arbitrary workspace of dimension `W`.  The oracle for a marked element `x` is the phase
oracle `oracle x`, which flips the sign of every basis vector whose query register holds
`x`.  An algorithm is an arbitrary sequence `U 0, U 1, …` of norm preserving linear maps
(unitaries), applied alternately with oracle calls to a unit initial state, see `run`.
The algorithm succeeds if measuring the query register of the final state returns the
marked element, i.e. if `‖proj x (run U (oracle x) init T)‖ ^ 2 ≥ 2/3`.
-/

namespace QI

open scoped BigOperators

/-- The state space of the algorithm: an `N`-dimensional query register tensored with a
`W`-dimensional workspace. -/
abbrev QState (N W : ℕ) := EuclideanSpace ℂ (Fin N × Fin W)

/-- The orthogonal projection onto the subspace where the query register holds `x`. -/

lemma norm_run_free {N W : ℕ} (U : ℕ → QState N W →ₗ[ℂ] QState N W)
    (hU : ∀ t v, ‖U t v‖ = ‖v‖) (init : QState N W) (t : ℕ) :
    ‖run U id init t‖ = ‖init‖ := by
  induction t with
  | zero => rfl
  | succ t ih => rw [run_succ, id, hU, ih]

/-- **The hybrid argument.**  The final state of the algorithm run with the oracle marking
`x` differs from the final state of the oracle-free run by at most twice the total
amplitude that the oracle-free run places on the branch `x`. -/
