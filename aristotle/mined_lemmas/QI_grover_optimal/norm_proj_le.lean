import Mathlib
/-!
# Grover Optimal
Category: Frontier Qi
Target: QI.grover_optimal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to be the first command of a module, so the header
-- module docstring above is placed immediately after the single `import Mathlib` line.)

/-!
## The BBBV lower bound for unstructured search

We formalise the Bennett–Bernstein–Brassard–Vazirani hybrid argument: any quantum
algorithm that finds a marked item among `N` possibilities with success probability
at least `2/3` must make `Ω(√N)` queries to the oracle.

**The model.**  The workspace is the finite dimensional Hilbert space
`QState N W = EuclideanSpace ℂ (Fin N × Fin W)`: an index register holding one of the
`N` candidate items, tensored with an arbitrary `W`-dimensional workspace.
For a marked item `x : Fin N`, the (phase) oracle `oracle x` flips the sign of every
basis vector whose index register equals `x`; it is a norm preserving linear map.
An algorithm consists of a unit initial state `psi0` and an arbitrary sequence
`U : ℕ → QState N W →ₗᵢ[ℂ] QState N W` of linear isometries (in particular every
unitary is allowed).  With oracle `x` the state after `t` queries is
`runOracle U psi0 x t`, and `runFree U psi0 t` is the corresponding oracle-free run.
The algorithm answers by measuring the index register of its final state, so its
success probability on input `x` is `‖proj x (runOracle U psi0 x T)‖ ^ 2`.

**The result** (`QI.grover_optimal`): if `6 ≤ N` and the algorithm succeeds with
probability at least `2/3` on *every* marked item `x`, then `√N / 20 ≤ T`.
Since Grover's algorithm achieves `O(√N)` queries, this is optimal up to constants.
-/

namespace QI

open Finset

/-- The state space of the search algorithm: an `N`-dimensional index register
tensored with a `W`-dimensional workspace. -/
abbrev QState (N W : ℕ) := EuclideanSpace ℂ (Fin N × Fin W)

variable {N W : ℕ}

/-- Orthogonal projection onto the subspace where the index register holds `x`. -/

lemma norm_proj_le (x : Fin N) (v : QState N W) : ‖proj x v‖ ≤ ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  refine Finset.sum_le_sum fun p _ => ?_
  simp only [proj_apply]
  split_ifs <;> simp

/-- Pythagoras: the squared norms of the components of a state sum to its squared norm. -/
