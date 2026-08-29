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

theorem no_communication_unitary (ρ : Matrix (m × n) (m × n) ℂ) (U : Matrix n n ℂ)
    (hU : Uᴴ * U = 1) :
    ptraceB (localB U * ρ * (localB U)ᴴ) = ptraceB ρ := by
  have h := no_communication (ι := Unit) ρ (fun _ => U) (by simpa using hU)
  simpa [applyB] using h

omit [DecidableEq m] in
/-- The expectation value of an observable `M` local to Alice depends on the global state only
through Alice's reduced state. -/
