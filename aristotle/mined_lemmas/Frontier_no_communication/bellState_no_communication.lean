/-
# No Communication
Category: Frontier Physics
Target: Frontier.no_communication
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# No Communication
Category: Frontier Physics
Target: Frontier.no_communication
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Local operations performed by Alice on her half of a bipartite (possibly entangled)
system cannot change Bob's reduced state, hence cannot transmit any information.

The bipartite system is modelled by matrices indexed by `A × B` over `ℂ`
(`A` = Alice's factor, `B` = Bob's factor).  Alice's local operation is an
arbitrary quantum channel given in Kraus form by operators `K i` acting on her
factor only, i.e. `K i ⊗ I`, subject to trace preservation `∑ i, (K i)ᴴ * K i = 1`.
Bob's reduced state is the partial trace over Alice's factor.
-/

namespace Frontier

open scoped Matrix
open Finset

variable {A B ι : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype ι]

/-- Partial trace over the first (Alice) factor of a bipartite operator:
Bob's reduced state. -/

theorem bellState_no_communication (K : ι → Matrix (Fin 2) (Fin 2) ℂ)
    (hK : ∑ i, (K i)ᴴ * (K i) = 1) :
    ptraceA (∑ i, locA (K i) * bellState * (locA (K i))ᴴ)
      = (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [no_communication K hK bellState, ptraceA_bellState]

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

