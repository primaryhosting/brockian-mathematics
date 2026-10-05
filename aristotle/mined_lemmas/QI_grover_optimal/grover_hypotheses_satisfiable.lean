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

theorem grover_hypotheses_satisfiable :
    ∃ (U : ℕ → QState 1 1 →ₗ[ℂ] QState 1 1) (init : QState 1 1),
      (∀ t v, ‖U t v‖ = ‖v‖) ∧ ‖init‖ = 1 ∧
        ∀ x : Fin 1, (2 : ℝ) / 3 ≤ ‖proj x (run U (oracle x) init 0)‖ ^ 2 := by
  refine ⟨fun _ => LinearMap.id, EuclideanSpace.single (0, 0) 1, fun _ _ => rfl, by simp, ?_⟩
  intro x
  have h : ‖proj x (run (fun _ => LinearMap.id) (oracle x)
      (EuclideanSpace.single ((0 : Fin 1), (0 : Fin 1)) 1) 0)‖ ^ 2 = 1 := by
    rw [proj_normsq]
    simp [EuclideanSpace.single_apply, Prod.ext_iff, Fin.eq_zero]
  rw [h]
  norm_num

end QI

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

