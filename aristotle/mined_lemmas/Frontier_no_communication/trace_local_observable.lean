import Mathlib

/-!
# No Communication
Category: Frontier Physics
Target: Frontier.no_communication
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Matrix Kronecker

namespace Frontier

variable {m n ι : Type*} [Fintype m] [Fintype n] [Fintype ι] [DecidableEq m] [DecidableEq n]

/-- The reduced state ("partial trace") of a bipartite density matrix on the `m`-factor
(Alice's system), obtained by tracing out the `n`-factor (Bob's system). -/

theorem trace_local_observable (ρ : Matrix (m × n) (m × n) ℂ) (M : Matrix m m ℂ) :
    (ρ * (M ⊗ₖ (1 : Matrix n n ℂ))).trace = (ptraceB ρ * M).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.kronecker_apply,
    Matrix.one_apply, ptraceB, Fintype.sum_prod_type, Finset.sum_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]

/-- **No communication, statistical form.**  No measurement Alice performs can detect whether
Bob applied a local channel to his half of the entangled pair: every local expectation value is
unchanged. -/
