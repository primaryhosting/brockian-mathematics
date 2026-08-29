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

theorem no_communication_expectation (ρ : Matrix (m × n) (m × n) ℂ) (K : ι → Matrix n n ℂ)
    (hK : ∑ a, (K a)ᴴ * (K a) = 1) (M : Matrix m m ℂ) :
    (applyB K ρ * (M ⊗ₖ (1 : Matrix n n ℂ))).trace = (ρ * (M ⊗ₖ (1 : Matrix n n ℂ))).trace := by
  rw [trace_local_observable, trace_local_observable, no_communication ρ K hK]

end Frontier

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

