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

noncomputable def localB (K : Matrix n n ℂ) : Matrix (m × n) (m × n) ℂ :=
  (1 : Matrix m m ℂ) ⊗ₖ K

/-- The action of a quantum channel on Bob's half, given in Kraus form by the family `K`. -/
