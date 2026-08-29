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

noncomputable def locA (K : Matrix A A ℂ) : Matrix (A × B) (A × B) ℂ :=
  fun p q => K p.1 q.1 * (if p.2 = q.2 then 1 else 0)

omit [DecidableEq A] [DecidableEq B] in
/-- Reordering a quadruple sum of complex numbers. -/
