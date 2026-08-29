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

lemma oracle_isometry {N W : ℕ} (x : Fin N) (u v : QState N W) :
    ‖oracle x u - oracle x v‖ = ‖u - v‖ := by
  have key : ‖oracle x u - oracle x v‖ ^ 2 = ‖u - v‖ ^ 2 := by
    rw [normsq, normsq]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [PiLp.sub_apply, oracle_apply]
    split_ifs with h
    · rw [show -u.ofLp p - -v.ofLp p = -(u.ofLp p - v.ofLp p) by ring, norm_neg]
    · rfl
  nlinarith [norm_nonneg (oracle x u - oracle x v), norm_nonneg (u - v)]

/-- A query only disturbs the state through the branch on which it acts. -/
